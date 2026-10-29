import BstLean.Part264Repair
/-! Rational envelope and frame checks for each dimension. -/
namespace BstLean.Part264
open Real Set BstLean.Part255 BstLean.Part263
noncomputable def cap12325 : Fin 43 → ℝ
  | ⟨0,_⟩ => (275945177 / 1000000000 : ℝ)
  | ⟨1,_⟩ => (1381739 / 5000000 : ℝ)
  | ⟨2,_⟩ => (27674943 / 100000000 : ℝ)
  | ⟨3,_⟩ => (138575031 / 500000000 : ℝ)
  | ⟨4,_⟩ => (55509941 / 200000000 : ℝ)
  | ⟨5,_⟩ => (138974179 / 500000000 : ℝ)
  | ⟨6,_⟩ => (278345551 / 1000000000 : ℝ)
  | ⟨7,_⟩ => (139371119 / 500000000 : ℝ)
  | ⟨8,_⟩ => (5582759 / 20000000 : ℝ)
  | ⟨9,_⟩ => (27953269 / 100000000 : ℝ)
  | ⟨10,_⟩ => (13996323 / 50000000 : ℝ)
  | ⟨11,_⟩ => (280318781 / 1000000000 : ℝ)
  | ⟨12,_⟩ => (140355313 / 500000000 : ℝ)
  | ⟨13,_⟩ => (8784407 / 31250000 : ℝ)
  | ⟨14,_⟩ => (56298271 / 200000000 : ℝ)
  | ⟨15,_⟩ => (281880587 / 1000000000 : ℝ)
  | ⟨16,_⟩ => (282268877 / 1000000000 : ℝ)
  | ⟨17,_⟩ => (56531247 / 200000000 : ℝ)
  | ⟨18,_⟩ => (56608531 / 200000000 : ℝ)
  | ⟨19,_⟩ => (283428147 / 1000000000 : ℝ)
  | ⟨20,_⟩ => (283812713 / 1000000000 : ℝ)
  | ⟨21,_⟩ => (142098181 / 500000000 : ℝ)
  | ⟨22,_⟩ => (17786193 / 62500000 : ℝ)
  | ⟨23,_⟩ => (284960403 / 1000000000 : ℝ)
  | ⟨24,_⟩ => (142670653 / 500000000 : ℝ)
  | ⟨25,_⟩ => (285720849 / 1000000000 : ℝ)
  | ⟨26,_⟩ => (286099987 / 1000000000 : ℝ)
  | ⟨27,_⟩ => (286477727 / 1000000000 : ℝ)
  | ⟨28,_⟩ => (286854571 / 1000000000 : ℝ)
  | ⟨29,_⟩ => (287230519 / 1000000000 : ℝ)
  | ⟨30,_⟩ => (143802537 / 500000000 : ℝ)
  | ⟨31,_⟩ => (57595849 / 200000000 : ℝ)
  | ⟨32,_⟩ => (36044067 / 125000000 : ℝ)
  | ⟨33,_⟩ => (288724437 / 1000000000 : ℝ)
  | ⟨34,_⟩ => (289095463 / 1000000000 : ℝ)
  | ⟨35,_⟩ => (289465619 / 1000000000 : ℝ)
  | ⟨36,_⟩ => (289834897 / 1000000000 : ℝ)
  | ⟨37,_⟩ => (290203317 / 1000000000 : ℝ)
  | ⟨38,_⟩ => (36321359 / 125000000 : ℝ)
  | ⟨39,_⟩ => (9091783 / 31250000 : ℝ)
  | ⟨40,_⟩ => (14565119 / 50000000 : ℝ)
  | ⟨41,_⟩ => (145833427 / 500000000 : ℝ)
  | ⟨42,_⟩ => (73007619 / 250000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12325Cell0 :
    0 ≤ cap12325 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12325 (parameters ⟨0,by decide⟩)
      (scalarRow12325.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12325 ⟨0,by decide⟩ ∧
    (scalarRow12325.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12325 ⟨0,by decide⟩ + (scalarRow12325.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12325.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12325.targetFrame := by
  norm_num [cap12325, scalarRow12325, sourceIndex, cell12325, BstLean.Part263.envelope, parameters]

theorem repair12325Cell1 :
    0 ≤ cap12325 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12325 (parameters ⟨1,by decide⟩)
      (scalarRow12325.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12325 ⟨1,by decide⟩ ∧
    (scalarRow12325.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12325 ⟨1,by decide⟩ + (scalarRow12325.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12325.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12325.targetFrame := by
  norm_num [cap12325, scalarRow12325, sourceIndex, cell12325, BstLean.Part263.envelope, parameters]

theorem repair12325Cell2 :
    0 ≤ cap12325 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12325 (parameters ⟨2,by decide⟩)
      (scalarRow12325.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12325 ⟨2,by decide⟩ ∧
    (scalarRow12325.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12325 ⟨2,by decide⟩ + (scalarRow12325.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12325.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12325.targetFrame := by
  norm_num [cap12325, scalarRow12325, sourceIndex, cell12325, BstLean.Part263.envelope, parameters]

theorem repair12325Cell3 :
    0 ≤ cap12325 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12325 (parameters ⟨3,by decide⟩)
      (scalarRow12325.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12325 ⟨3,by decide⟩ ∧
    (scalarRow12325.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12325 ⟨3,by decide⟩ + (scalarRow12325.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12325.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12325.targetFrame := by
  norm_num [cap12325, scalarRow12325, sourceIndex, cell12325, BstLean.Part263.envelope, parameters]

theorem repair12325Cell4 :
    0 ≤ cap12325 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12325 (parameters ⟨4,by decide⟩)
      (scalarRow12325.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12325 ⟨4,by decide⟩ ∧
    (scalarRow12325.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12325 ⟨4,by decide⟩ + (scalarRow12325.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12325.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12325.targetFrame := by
  norm_num [cap12325, scalarRow12325, sourceIndex, cell12325, BstLean.Part263.envelope, parameters]

theorem repair12325Cell5 :
    0 ≤ cap12325 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12325 (parameters ⟨5,by decide⟩)
      (scalarRow12325.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12325 ⟨5,by decide⟩ ∧
    (scalarRow12325.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12325 ⟨5,by decide⟩ + (scalarRow12325.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12325.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12325.targetFrame := by
  norm_num [cap12325, scalarRow12325, sourceIndex, cell12325, BstLean.Part263.envelope, parameters]

theorem repair12325Cell6 :
    0 ≤ cap12325 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12325 (parameters ⟨6,by decide⟩)
      (scalarRow12325.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12325 ⟨6,by decide⟩ ∧
    (scalarRow12325.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12325 ⟨6,by decide⟩ + (scalarRow12325.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12325.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12325.targetFrame := by
  norm_num [cap12325, scalarRow12325, sourceIndex, cell12325, BstLean.Part263.envelope, parameters]

theorem repair12325Cell7 :
    0 ≤ cap12325 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12325 (parameters ⟨7,by decide⟩)
      (scalarRow12325.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12325 ⟨7,by decide⟩ ∧
    (scalarRow12325.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12325 ⟨7,by decide⟩ + (scalarRow12325.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12325.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12325.targetFrame := by
  norm_num [cap12325, scalarRow12325, sourceIndex, cell12325, BstLean.Part263.envelope, parameters]

theorem repair12325Cell8 :
    0 ≤ cap12325 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12325 (parameters ⟨8,by decide⟩)
      (scalarRow12325.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12325 ⟨8,by decide⟩ ∧
    (scalarRow12325.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12325 ⟨8,by decide⟩ + (scalarRow12325.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12325.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12325.targetFrame := by
  norm_num [cap12325, scalarRow12325, sourceIndex, cell12325, BstLean.Part263.envelope, parameters]

theorem repair12325Cell9 :
    0 ≤ cap12325 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12325 (parameters ⟨9,by decide⟩)
      (scalarRow12325.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12325 ⟨9,by decide⟩ ∧
    (scalarRow12325.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12325 ⟨9,by decide⟩ + (scalarRow12325.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12325.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12325.targetFrame := by
  norm_num [cap12325, scalarRow12325, sourceIndex, cell12325, BstLean.Part263.envelope, parameters]

theorem repair12325Cell10 :
    0 ≤ cap12325 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12325 (parameters ⟨10,by decide⟩)
      (scalarRow12325.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12325 ⟨10,by decide⟩ ∧
    (scalarRow12325.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12325 ⟨10,by decide⟩ + (scalarRow12325.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12325.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12325.targetFrame := by
  norm_num [cap12325, scalarRow12325, sourceIndex, cell12325, BstLean.Part263.envelope, parameters]

theorem repair12325Cell11 :
    0 ≤ cap12325 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12325 (parameters ⟨11,by decide⟩)
      (scalarRow12325.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12325 ⟨11,by decide⟩ ∧
    (scalarRow12325.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12325 ⟨11,by decide⟩ + (scalarRow12325.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12325.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12325.targetFrame := by
  norm_num [cap12325, scalarRow12325, sourceIndex, cell12325, BstLean.Part263.envelope, parameters]

theorem repair12325Cell12 :
    0 ≤ cap12325 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12325 (parameters ⟨12,by decide⟩)
      (scalarRow12325.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12325 ⟨12,by decide⟩ ∧
    (scalarRow12325.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12325 ⟨12,by decide⟩ + (scalarRow12325.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12325.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12325.targetFrame := by
  norm_num [cap12325, scalarRow12325, sourceIndex, cell12325, BstLean.Part263.envelope, parameters]

theorem repair12325Cell13 :
    0 ≤ cap12325 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12325 (parameters ⟨13,by decide⟩)
      (scalarRow12325.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12325 ⟨13,by decide⟩ ∧
    (scalarRow12325.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12325 ⟨13,by decide⟩ + (scalarRow12325.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12325.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12325.targetFrame := by
  norm_num [cap12325, scalarRow12325, sourceIndex, cell12325, BstLean.Part263.envelope, parameters]

theorem repair12325Cell14 :
    0 ≤ cap12325 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12325 (parameters ⟨14,by decide⟩)
      (scalarRow12325.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12325 ⟨14,by decide⟩ ∧
    (scalarRow12325.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12325 ⟨14,by decide⟩ + (scalarRow12325.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12325.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12325.targetFrame := by
  norm_num [cap12325, scalarRow12325, sourceIndex, cell12325, BstLean.Part263.envelope, parameters]

theorem repair12325Cell15 :
    0 ≤ cap12325 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12325 (parameters ⟨15,by decide⟩)
      (scalarRow12325.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12325 ⟨15,by decide⟩ ∧
    (scalarRow12325.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12325 ⟨15,by decide⟩ + (scalarRow12325.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12325.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12325.targetFrame := by
  norm_num [cap12325, scalarRow12325, sourceIndex, cell12325, BstLean.Part263.envelope, parameters]

theorem repair12325Cell16 :
    0 ≤ cap12325 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12325 (parameters ⟨16,by decide⟩)
      (scalarRow12325.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12325 ⟨16,by decide⟩ ∧
    (scalarRow12325.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12325 ⟨16,by decide⟩ + (scalarRow12325.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12325.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12325.targetFrame := by
  norm_num [cap12325, scalarRow12325, sourceIndex, cell12325, BstLean.Part263.envelope, parameters]

theorem repair12325Cell17 :
    0 ≤ cap12325 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12325 (parameters ⟨17,by decide⟩)
      (scalarRow12325.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12325 ⟨17,by decide⟩ ∧
    (scalarRow12325.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12325 ⟨17,by decide⟩ + (scalarRow12325.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12325.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12325.targetFrame := by
  norm_num [cap12325, scalarRow12325, sourceIndex, cell12325, BstLean.Part263.envelope, parameters]

theorem repair12325Cell18 :
    0 ≤ cap12325 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12325 (parameters ⟨18,by decide⟩)
      (scalarRow12325.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12325 ⟨18,by decide⟩ ∧
    (scalarRow12325.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12325 ⟨18,by decide⟩ + (scalarRow12325.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12325.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12325.targetFrame := by
  norm_num [cap12325, scalarRow12325, sourceIndex, cell12325, BstLean.Part263.envelope, parameters]

theorem repair12325Cell19 :
    0 ≤ cap12325 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12325 (parameters ⟨19,by decide⟩)
      (scalarRow12325.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12325 ⟨19,by decide⟩ ∧
    (scalarRow12325.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12325 ⟨19,by decide⟩ + (scalarRow12325.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12325.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12325.targetFrame := by
  norm_num [cap12325, scalarRow12325, sourceIndex, cell12325, BstLean.Part263.envelope, parameters]

theorem repair12325Cell20 :
    0 ≤ cap12325 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12325 (parameters ⟨20,by decide⟩)
      (scalarRow12325.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12325 ⟨20,by decide⟩ ∧
    (scalarRow12325.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12325 ⟨20,by decide⟩ + (scalarRow12325.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12325.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12325.targetFrame := by
  norm_num [cap12325, scalarRow12325, sourceIndex, cell12325, BstLean.Part263.envelope, parameters]

theorem repair12325Cell21 :
    0 ≤ cap12325 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12325 (parameters ⟨21,by decide⟩)
      (scalarRow12325.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12325 ⟨21,by decide⟩ ∧
    (scalarRow12325.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12325 ⟨21,by decide⟩ + (scalarRow12325.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12325.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12325.targetFrame := by
  norm_num [cap12325, scalarRow12325, sourceIndex, cell12325, BstLean.Part263.envelope, parameters]

theorem repair12325Cell22 :
    0 ≤ cap12325 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12325 (parameters ⟨22,by decide⟩)
      (scalarRow12325.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12325 ⟨22,by decide⟩ ∧
    (scalarRow12325.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12325 ⟨22,by decide⟩ + (scalarRow12325.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12325.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12325.targetFrame := by
  norm_num [cap12325, scalarRow12325, sourceIndex, cell12325, BstLean.Part263.envelope, parameters]

theorem repair12325Cell23 :
    0 ≤ cap12325 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12325 (parameters ⟨23,by decide⟩)
      (scalarRow12325.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12325 ⟨23,by decide⟩ ∧
    (scalarRow12325.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12325 ⟨23,by decide⟩ + (scalarRow12325.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12325.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12325.targetFrame := by
  norm_num [cap12325, scalarRow12325, sourceIndex, cell12325, BstLean.Part263.envelope, parameters]

theorem repair12325Cell24 :
    0 ≤ cap12325 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12325 (parameters ⟨24,by decide⟩)
      (scalarRow12325.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12325 ⟨24,by decide⟩ ∧
    (scalarRow12325.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12325 ⟨24,by decide⟩ + (scalarRow12325.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12325.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12325.targetFrame := by
  norm_num [cap12325, scalarRow12325, sourceIndex, cell12325, BstLean.Part263.envelope, parameters]

theorem repair12325Cell25 :
    0 ≤ cap12325 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12325 (parameters ⟨25,by decide⟩)
      (scalarRow12325.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12325 ⟨25,by decide⟩ ∧
    (scalarRow12325.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12325 ⟨25,by decide⟩ + (scalarRow12325.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12325.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12325.targetFrame := by
  norm_num [cap12325, scalarRow12325, sourceIndex, cell12325, BstLean.Part263.envelope, parameters]

theorem repair12325Cell26 :
    0 ≤ cap12325 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12325 (parameters ⟨26,by decide⟩)
      (scalarRow12325.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12325 ⟨26,by decide⟩ ∧
    (scalarRow12325.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12325 ⟨26,by decide⟩ + (scalarRow12325.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12325.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12325.targetFrame := by
  norm_num [cap12325, scalarRow12325, sourceIndex, cell12325, BstLean.Part263.envelope, parameters]

theorem repair12325Cell27 :
    0 ≤ cap12325 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12325 (parameters ⟨27,by decide⟩)
      (scalarRow12325.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12325 ⟨27,by decide⟩ ∧
    (scalarRow12325.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12325 ⟨27,by decide⟩ + (scalarRow12325.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12325.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12325.targetFrame := by
  norm_num [cap12325, scalarRow12325, sourceIndex, cell12325, BstLean.Part263.envelope, parameters]

theorem repair12325Cell28 :
    0 ≤ cap12325 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12325 (parameters ⟨28,by decide⟩)
      (scalarRow12325.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12325 ⟨28,by decide⟩ ∧
    (scalarRow12325.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12325 ⟨28,by decide⟩ + (scalarRow12325.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12325.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12325.targetFrame := by
  norm_num [cap12325, scalarRow12325, sourceIndex, cell12325, BstLean.Part263.envelope, parameters]

theorem repair12325Cell29 :
    0 ≤ cap12325 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12325 (parameters ⟨29,by decide⟩)
      (scalarRow12325.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12325 ⟨29,by decide⟩ ∧
    (scalarRow12325.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12325 ⟨29,by decide⟩ + (scalarRow12325.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12325.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12325.targetFrame := by
  norm_num [cap12325, scalarRow12325, sourceIndex, cell12325, BstLean.Part263.envelope, parameters]

theorem repair12325Cell30 :
    0 ≤ cap12325 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12325 (parameters ⟨30,by decide⟩)
      (scalarRow12325.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12325 ⟨30,by decide⟩ ∧
    (scalarRow12325.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12325 ⟨30,by decide⟩ + (scalarRow12325.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12325.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12325.targetFrame := by
  norm_num [cap12325, scalarRow12325, sourceIndex, cell12325, BstLean.Part263.envelope, parameters]

theorem repair12325Cell31 :
    0 ≤ cap12325 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12325 (parameters ⟨31,by decide⟩)
      (scalarRow12325.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12325 ⟨31,by decide⟩ ∧
    (scalarRow12325.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12325 ⟨31,by decide⟩ + (scalarRow12325.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12325.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12325.targetFrame := by
  norm_num [cap12325, scalarRow12325, sourceIndex, cell12325, BstLean.Part263.envelope, parameters]

theorem repair12325Cell32 :
    0 ≤ cap12325 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12325 (parameters ⟨32,by decide⟩)
      (scalarRow12325.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12325 ⟨32,by decide⟩ ∧
    (scalarRow12325.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12325 ⟨32,by decide⟩ + (scalarRow12325.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12325.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12325.targetFrame := by
  norm_num [cap12325, scalarRow12325, sourceIndex, cell12325, BstLean.Part263.envelope, parameters]

theorem repair12325Cell33 :
    0 ≤ cap12325 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12325 (parameters ⟨33,by decide⟩)
      (scalarRow12325.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12325 ⟨33,by decide⟩ ∧
    (scalarRow12325.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12325 ⟨33,by decide⟩ + (scalarRow12325.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12325.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12325.targetFrame := by
  norm_num [cap12325, scalarRow12325, sourceIndex, cell12325, BstLean.Part263.envelope, parameters]

theorem repair12325Cell34 :
    0 ≤ cap12325 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12325 (parameters ⟨34,by decide⟩)
      (scalarRow12325.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12325 ⟨34,by decide⟩ ∧
    (scalarRow12325.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12325 ⟨34,by decide⟩ + (scalarRow12325.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12325.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12325.targetFrame := by
  norm_num [cap12325, scalarRow12325, sourceIndex, cell12325, BstLean.Part263.envelope, parameters]

theorem repair12325Cell35 :
    0 ≤ cap12325 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12325 (parameters ⟨35,by decide⟩)
      (scalarRow12325.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12325 ⟨35,by decide⟩ ∧
    (scalarRow12325.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12325 ⟨35,by decide⟩ + (scalarRow12325.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12325.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12325.targetFrame := by
  norm_num [cap12325, scalarRow12325, sourceIndex, cell12325, BstLean.Part263.envelope, parameters]

theorem repair12325Cell36 :
    0 ≤ cap12325 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12325 (parameters ⟨36,by decide⟩)
      (scalarRow12325.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12325 ⟨36,by decide⟩ ∧
    (scalarRow12325.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12325 ⟨36,by decide⟩ + (scalarRow12325.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12325.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12325.targetFrame := by
  norm_num [cap12325, scalarRow12325, sourceIndex, cell12325, BstLean.Part263.envelope, parameters]

theorem repair12325Cell37 :
    0 ≤ cap12325 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12325 (parameters ⟨37,by decide⟩)
      (scalarRow12325.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12325 ⟨37,by decide⟩ ∧
    (scalarRow12325.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12325 ⟨37,by decide⟩ + (scalarRow12325.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12325.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12325.targetFrame := by
  norm_num [cap12325, scalarRow12325, sourceIndex, cell12325, BstLean.Part263.envelope, parameters]

theorem repair12325Cell38 :
    0 ≤ cap12325 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12325 (parameters ⟨38,by decide⟩)
      (scalarRow12325.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12325 ⟨38,by decide⟩ ∧
    (scalarRow12325.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12325 ⟨38,by decide⟩ + (scalarRow12325.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12325.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12325.targetFrame := by
  norm_num [cap12325, scalarRow12325, sourceIndex, cell12325, BstLean.Part263.envelope, parameters]

theorem repair12325Cell39 :
    0 ≤ cap12325 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12325 (parameters ⟨39,by decide⟩)
      (scalarRow12325.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12325 ⟨39,by decide⟩ ∧
    (scalarRow12325.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12325 ⟨39,by decide⟩ + (scalarRow12325.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12325.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12325.targetFrame := by
  norm_num [cap12325, scalarRow12325, sourceIndex, cell12325, BstLean.Part263.envelope, parameters]

theorem repair12325Cell40 :
    0 ≤ cap12325 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12325 (parameters ⟨40,by decide⟩)
      (scalarRow12325.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12325 ⟨40,by decide⟩ ∧
    (scalarRow12325.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12325 ⟨40,by decide⟩ + (scalarRow12325.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12325.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12325.targetFrame := by
  norm_num [cap12325, scalarRow12325, sourceIndex, cell12325, BstLean.Part263.envelope, parameters]

theorem repair12325Cell41 :
    0 ≤ cap12325 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12325 (parameters ⟨41,by decide⟩)
      (scalarRow12325.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12325 ⟨41,by decide⟩ ∧
    (scalarRow12325.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12325 ⟨41,by decide⟩ + (scalarRow12325.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12325.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12325.targetFrame := by
  norm_num [cap12325, scalarRow12325, sourceIndex, cell12325, BstLean.Part263.envelope, parameters]

theorem repair12325Cell42 :
    0 ≤ cap12325 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12325 (parameters ⟨42,by decide⟩)
      (scalarRow12325.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12325 ⟨42,by decide⟩ ∧
    (scalarRow12325.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12325 ⟨42,by decide⟩ + (scalarRow12325.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12325.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12325.targetFrame := by
  norm_num [cap12325, scalarRow12325, sourceIndex, cell12325, BstLean.Part263.envelope, parameters]

theorem repair12325Cells (j : Fin 43) :
    0 ≤ cap12325 j ∧
    BstLean.Part263.envelope 12325 (parameters j) (scalarRow12325.table (sourceIndex j)).upper ≤ cap12325 j ∧
    (scalarRow12325.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12325 j + (scalarRow12325.table (sourceIndex j)).centre) /
      (scalarRow12325.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12325.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12325Cell0
  | ⟨1,_⟩ => exact repair12325Cell1
  | ⟨2,_⟩ => exact repair12325Cell2
  | ⟨3,_⟩ => exact repair12325Cell3
  | ⟨4,_⟩ => exact repair12325Cell4
  | ⟨5,_⟩ => exact repair12325Cell5
  | ⟨6,_⟩ => exact repair12325Cell6
  | ⟨7,_⟩ => exact repair12325Cell7
  | ⟨8,_⟩ => exact repair12325Cell8
  | ⟨9,_⟩ => exact repair12325Cell9
  | ⟨10,_⟩ => exact repair12325Cell10
  | ⟨11,_⟩ => exact repair12325Cell11
  | ⟨12,_⟩ => exact repair12325Cell12
  | ⟨13,_⟩ => exact repair12325Cell13
  | ⟨14,_⟩ => exact repair12325Cell14
  | ⟨15,_⟩ => exact repair12325Cell15
  | ⟨16,_⟩ => exact repair12325Cell16
  | ⟨17,_⟩ => exact repair12325Cell17
  | ⟨18,_⟩ => exact repair12325Cell18
  | ⟨19,_⟩ => exact repair12325Cell19
  | ⟨20,_⟩ => exact repair12325Cell20
  | ⟨21,_⟩ => exact repair12325Cell21
  | ⟨22,_⟩ => exact repair12325Cell22
  | ⟨23,_⟩ => exact repair12325Cell23
  | ⟨24,_⟩ => exact repair12325Cell24
  | ⟨25,_⟩ => exact repair12325Cell25
  | ⟨26,_⟩ => exact repair12325Cell26
  | ⟨27,_⟩ => exact repair12325Cell27
  | ⟨28,_⟩ => exact repair12325Cell28
  | ⟨29,_⟩ => exact repair12325Cell29
  | ⟨30,_⟩ => exact repair12325Cell30
  | ⟨31,_⟩ => exact repair12325Cell31
  | ⟨32,_⟩ => exact repair12325Cell32
  | ⟨33,_⟩ => exact repair12325Cell33
  | ⟨34,_⟩ => exact repair12325Cell34
  | ⟨35,_⟩ => exact repair12325Cell35
  | ⟨36,_⟩ => exact repair12325Cell36
  | ⟨37,_⟩ => exact repair12325Cell37
  | ⟨38,_⟩ => exact repair12325Cell38
  | ⟨39,_⟩ => exact repair12325Cell39
  | ⟨40,_⟩ => exact repair12325Cell40
  | ⟨41,_⟩ => exact repair12325Cell41
  | ⟨42,_⟩ => exact repair12325Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12325 : FrameRepair 12325 scalarRow12325 where
  cap := cap12325
  cap_nonneg := fun j => (repair12325Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12325])
  endpoint := fun j => (repair12325Cells j).2.1
  endpoint_upper := fun j => (repair12325Cells j).2.2.1
  frame := fun j => (repair12325Cells j).2.2.2

noncomputable def cap12326 : Fin 43 → ℝ
  | ⟨0,_⟩ => (137972551 / 500000000 : ℝ)
  | ⟨1,_⟩ => (276347719 / 1000000000 : ℝ)
  | ⟨2,_⟩ => (138374671 / 500000000 : ℝ)
  | ⟨3,_⟩ => (17321873 / 62500000 : ℝ)
  | ⟨4,_⟩ => (69387401 / 250000000 : ℝ)
  | ⟨5,_⟩ => (277948251 / 1000000000 : ℝ)
  | ⟨6,_⟩ => (278345437 / 1000000000 : ℝ)
  | ⟨7,_⟩ => (139371059 / 500000000 : ℝ)
  | ⟨8,_⟩ => (8723057 / 31250000 : ℝ)
  | ⟨9,_⟩ => (279532557 / 1000000000 : ℝ)
  | ⟨10,_⟩ => (279926321 / 1000000000 : ℝ)
  | ⟨11,_⟩ => (70079659 / 250000000 : ℝ)
  | ⟨12,_⟩ => (140355237 / 500000000 : ℝ)
  | ⟨13,_⟩ => (140550433 / 500000000 : ℝ)
  | ⟨14,_⟩ => (281491191 / 1000000000 : ℝ)
  | ⟨15,_⟩ => (8808763 / 31250000 : ℝ)
  | ⟨16,_⟩ => (2822687 / 10000000 : ℝ)
  | ⟨17,_⟩ => (282656053 / 1000000000 : ℝ)
  | ⟨18,_⟩ => (141521233 / 500000000 : ℝ)
  | ⟨19,_⟩ => (17714247 / 62500000 : ℝ)
  | ⟨20,_⟩ => (283812511 / 1000000000 : ℝ)
  | ⟨21,_⟩ => (142098077 / 500000000 : ℝ)
  | ⟨22,_⟩ => (142289437 / 500000000 : ℝ)
  | ⟨23,_⟩ => (284960183 / 1000000000 : ℝ)
  | ⟨24,_⟩ => (7133527 / 25000000 : ℝ)
  | ⟨25,_⟩ => (285720617 / 1000000000 : ℝ)
  | ⟨26,_⟩ => (286099749 / 1000000000 : ℝ)
  | ⟨27,_⟩ => (286477483 / 1000000000 : ℝ)
  | ⟨28,_⟩ => (3585679 / 12500000 : ℝ)
  | ⟨29,_⟩ => (143615131 / 500000000 : ℝ)
  | ⟨30,_⟩ => (287604811 / 1000000000 : ℝ)
  | ⟨31,_⟩ => (287978977 / 1000000000 : ℝ)
  | ⟨32,_⟩ => (288352261 / 1000000000 : ℝ)
  | ⟨33,_⟩ => (72181039 / 250000000 : ℝ)
  | ⟨34,_⟩ => (289095177 / 1000000000 : ℝ)
  | ⟨35,_⟩ => (144732663 / 500000000 : ℝ)
  | ⟨36,_⟩ => (289834599 / 1000000000 : ℝ)
  | ⟨37,_⟩ => (72550753 / 250000000 : ℝ)
  | ⟨38,_⟩ => (145285281 / 500000000 : ℝ)
  | ⟨39,_⟩ => (290936739 / 1000000000 : ℝ)
  | ⟨40,_⟩ => (145651029 / 500000000 : ℝ)
  | ⟨41,_⟩ => (11666661 / 40000000 : ℝ)
  | ⟨42,_⟩ => (146015071 / 500000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12326Cell0 :
    0 ≤ cap12326 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12326 (parameters ⟨0,by decide⟩)
      (scalarRow12326.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12326 ⟨0,by decide⟩ ∧
    (scalarRow12326.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12326 ⟨0,by decide⟩ + (scalarRow12326.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12326.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12326.targetFrame := by
  norm_num [cap12326, scalarRow12326, sourceIndex, cell12326, BstLean.Part263.envelope, parameters]

theorem repair12326Cell1 :
    0 ≤ cap12326 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12326 (parameters ⟨1,by decide⟩)
      (scalarRow12326.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12326 ⟨1,by decide⟩ ∧
    (scalarRow12326.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12326 ⟨1,by decide⟩ + (scalarRow12326.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12326.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12326.targetFrame := by
  norm_num [cap12326, scalarRow12326, sourceIndex, cell12326, BstLean.Part263.envelope, parameters]

theorem repair12326Cell2 :
    0 ≤ cap12326 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12326 (parameters ⟨2,by decide⟩)
      (scalarRow12326.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12326 ⟨2,by decide⟩ ∧
    (scalarRow12326.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12326 ⟨2,by decide⟩ + (scalarRow12326.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12326.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12326.targetFrame := by
  norm_num [cap12326, scalarRow12326, sourceIndex, cell12326, BstLean.Part263.envelope, parameters]

theorem repair12326Cell3 :
    0 ≤ cap12326 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12326 (parameters ⟨3,by decide⟩)
      (scalarRow12326.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12326 ⟨3,by decide⟩ ∧
    (scalarRow12326.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12326 ⟨3,by decide⟩ + (scalarRow12326.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12326.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12326.targetFrame := by
  norm_num [cap12326, scalarRow12326, sourceIndex, cell12326, BstLean.Part263.envelope, parameters]

theorem repair12326Cell4 :
    0 ≤ cap12326 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12326 (parameters ⟨4,by decide⟩)
      (scalarRow12326.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12326 ⟨4,by decide⟩ ∧
    (scalarRow12326.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12326 ⟨4,by decide⟩ + (scalarRow12326.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12326.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12326.targetFrame := by
  norm_num [cap12326, scalarRow12326, sourceIndex, cell12326, BstLean.Part263.envelope, parameters]

theorem repair12326Cell5 :
    0 ≤ cap12326 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12326 (parameters ⟨5,by decide⟩)
      (scalarRow12326.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12326 ⟨5,by decide⟩ ∧
    (scalarRow12326.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12326 ⟨5,by decide⟩ + (scalarRow12326.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12326.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12326.targetFrame := by
  norm_num [cap12326, scalarRow12326, sourceIndex, cell12326, BstLean.Part263.envelope, parameters]

theorem repair12326Cell6 :
    0 ≤ cap12326 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12326 (parameters ⟨6,by decide⟩)
      (scalarRow12326.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12326 ⟨6,by decide⟩ ∧
    (scalarRow12326.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12326 ⟨6,by decide⟩ + (scalarRow12326.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12326.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12326.targetFrame := by
  norm_num [cap12326, scalarRow12326, sourceIndex, cell12326, BstLean.Part263.envelope, parameters]

theorem repair12326Cell7 :
    0 ≤ cap12326 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12326 (parameters ⟨7,by decide⟩)
      (scalarRow12326.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12326 ⟨7,by decide⟩ ∧
    (scalarRow12326.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12326 ⟨7,by decide⟩ + (scalarRow12326.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12326.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12326.targetFrame := by
  norm_num [cap12326, scalarRow12326, sourceIndex, cell12326, BstLean.Part263.envelope, parameters]

theorem repair12326Cell8 :
    0 ≤ cap12326 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12326 (parameters ⟨8,by decide⟩)
      (scalarRow12326.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12326 ⟨8,by decide⟩ ∧
    (scalarRow12326.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12326 ⟨8,by decide⟩ + (scalarRow12326.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12326.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12326.targetFrame := by
  norm_num [cap12326, scalarRow12326, sourceIndex, cell12326, BstLean.Part263.envelope, parameters]

theorem repair12326Cell9 :
    0 ≤ cap12326 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12326 (parameters ⟨9,by decide⟩)
      (scalarRow12326.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12326 ⟨9,by decide⟩ ∧
    (scalarRow12326.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12326 ⟨9,by decide⟩ + (scalarRow12326.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12326.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12326.targetFrame := by
  norm_num [cap12326, scalarRow12326, sourceIndex, cell12326, BstLean.Part263.envelope, parameters]

theorem repair12326Cell10 :
    0 ≤ cap12326 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12326 (parameters ⟨10,by decide⟩)
      (scalarRow12326.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12326 ⟨10,by decide⟩ ∧
    (scalarRow12326.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12326 ⟨10,by decide⟩ + (scalarRow12326.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12326.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12326.targetFrame := by
  norm_num [cap12326, scalarRow12326, sourceIndex, cell12326, BstLean.Part263.envelope, parameters]

theorem repair12326Cell11 :
    0 ≤ cap12326 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12326 (parameters ⟨11,by decide⟩)
      (scalarRow12326.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12326 ⟨11,by decide⟩ ∧
    (scalarRow12326.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12326 ⟨11,by decide⟩ + (scalarRow12326.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12326.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12326.targetFrame := by
  norm_num [cap12326, scalarRow12326, sourceIndex, cell12326, BstLean.Part263.envelope, parameters]

theorem repair12326Cell12 :
    0 ≤ cap12326 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12326 (parameters ⟨12,by decide⟩)
      (scalarRow12326.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12326 ⟨12,by decide⟩ ∧
    (scalarRow12326.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12326 ⟨12,by decide⟩ + (scalarRow12326.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12326.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12326.targetFrame := by
  norm_num [cap12326, scalarRow12326, sourceIndex, cell12326, BstLean.Part263.envelope, parameters]

theorem repair12326Cell13 :
    0 ≤ cap12326 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12326 (parameters ⟨13,by decide⟩)
      (scalarRow12326.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12326 ⟨13,by decide⟩ ∧
    (scalarRow12326.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12326 ⟨13,by decide⟩ + (scalarRow12326.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12326.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12326.targetFrame := by
  norm_num [cap12326, scalarRow12326, sourceIndex, cell12326, BstLean.Part263.envelope, parameters]

theorem repair12326Cell14 :
    0 ≤ cap12326 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12326 (parameters ⟨14,by decide⟩)
      (scalarRow12326.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12326 ⟨14,by decide⟩ ∧
    (scalarRow12326.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12326 ⟨14,by decide⟩ + (scalarRow12326.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12326.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12326.targetFrame := by
  norm_num [cap12326, scalarRow12326, sourceIndex, cell12326, BstLean.Part263.envelope, parameters]

theorem repair12326Cell15 :
    0 ≤ cap12326 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12326 (parameters ⟨15,by decide⟩)
      (scalarRow12326.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12326 ⟨15,by decide⟩ ∧
    (scalarRow12326.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12326 ⟨15,by decide⟩ + (scalarRow12326.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12326.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12326.targetFrame := by
  norm_num [cap12326, scalarRow12326, sourceIndex, cell12326, BstLean.Part263.envelope, parameters]

theorem repair12326Cell16 :
    0 ≤ cap12326 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12326 (parameters ⟨16,by decide⟩)
      (scalarRow12326.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12326 ⟨16,by decide⟩ ∧
    (scalarRow12326.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12326 ⟨16,by decide⟩ + (scalarRow12326.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12326.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12326.targetFrame := by
  norm_num [cap12326, scalarRow12326, sourceIndex, cell12326, BstLean.Part263.envelope, parameters]

theorem repair12326Cell17 :
    0 ≤ cap12326 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12326 (parameters ⟨17,by decide⟩)
      (scalarRow12326.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12326 ⟨17,by decide⟩ ∧
    (scalarRow12326.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12326 ⟨17,by decide⟩ + (scalarRow12326.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12326.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12326.targetFrame := by
  norm_num [cap12326, scalarRow12326, sourceIndex, cell12326, BstLean.Part263.envelope, parameters]

theorem repair12326Cell18 :
    0 ≤ cap12326 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12326 (parameters ⟨18,by decide⟩)
      (scalarRow12326.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12326 ⟨18,by decide⟩ ∧
    (scalarRow12326.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12326 ⟨18,by decide⟩ + (scalarRow12326.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12326.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12326.targetFrame := by
  norm_num [cap12326, scalarRow12326, sourceIndex, cell12326, BstLean.Part263.envelope, parameters]

theorem repair12326Cell19 :
    0 ≤ cap12326 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12326 (parameters ⟨19,by decide⟩)
      (scalarRow12326.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12326 ⟨19,by decide⟩ ∧
    (scalarRow12326.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12326 ⟨19,by decide⟩ + (scalarRow12326.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12326.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12326.targetFrame := by
  norm_num [cap12326, scalarRow12326, sourceIndex, cell12326, BstLean.Part263.envelope, parameters]

theorem repair12326Cell20 :
    0 ≤ cap12326 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12326 (parameters ⟨20,by decide⟩)
      (scalarRow12326.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12326 ⟨20,by decide⟩ ∧
    (scalarRow12326.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12326 ⟨20,by decide⟩ + (scalarRow12326.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12326.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12326.targetFrame := by
  norm_num [cap12326, scalarRow12326, sourceIndex, cell12326, BstLean.Part263.envelope, parameters]

theorem repair12326Cell21 :
    0 ≤ cap12326 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12326 (parameters ⟨21,by decide⟩)
      (scalarRow12326.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12326 ⟨21,by decide⟩ ∧
    (scalarRow12326.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12326 ⟨21,by decide⟩ + (scalarRow12326.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12326.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12326.targetFrame := by
  norm_num [cap12326, scalarRow12326, sourceIndex, cell12326, BstLean.Part263.envelope, parameters]

theorem repair12326Cell22 :
    0 ≤ cap12326 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12326 (parameters ⟨22,by decide⟩)
      (scalarRow12326.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12326 ⟨22,by decide⟩ ∧
    (scalarRow12326.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12326 ⟨22,by decide⟩ + (scalarRow12326.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12326.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12326.targetFrame := by
  norm_num [cap12326, scalarRow12326, sourceIndex, cell12326, BstLean.Part263.envelope, parameters]

theorem repair12326Cell23 :
    0 ≤ cap12326 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12326 (parameters ⟨23,by decide⟩)
      (scalarRow12326.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12326 ⟨23,by decide⟩ ∧
    (scalarRow12326.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12326 ⟨23,by decide⟩ + (scalarRow12326.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12326.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12326.targetFrame := by
  norm_num [cap12326, scalarRow12326, sourceIndex, cell12326, BstLean.Part263.envelope, parameters]

theorem repair12326Cell24 :
    0 ≤ cap12326 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12326 (parameters ⟨24,by decide⟩)
      (scalarRow12326.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12326 ⟨24,by decide⟩ ∧
    (scalarRow12326.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12326 ⟨24,by decide⟩ + (scalarRow12326.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12326.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12326.targetFrame := by
  norm_num [cap12326, scalarRow12326, sourceIndex, cell12326, BstLean.Part263.envelope, parameters]

theorem repair12326Cell25 :
    0 ≤ cap12326 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12326 (parameters ⟨25,by decide⟩)
      (scalarRow12326.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12326 ⟨25,by decide⟩ ∧
    (scalarRow12326.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12326 ⟨25,by decide⟩ + (scalarRow12326.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12326.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12326.targetFrame := by
  norm_num [cap12326, scalarRow12326, sourceIndex, cell12326, BstLean.Part263.envelope, parameters]

theorem repair12326Cell26 :
    0 ≤ cap12326 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12326 (parameters ⟨26,by decide⟩)
      (scalarRow12326.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12326 ⟨26,by decide⟩ ∧
    (scalarRow12326.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12326 ⟨26,by decide⟩ + (scalarRow12326.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12326.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12326.targetFrame := by
  norm_num [cap12326, scalarRow12326, sourceIndex, cell12326, BstLean.Part263.envelope, parameters]

theorem repair12326Cell27 :
    0 ≤ cap12326 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12326 (parameters ⟨27,by decide⟩)
      (scalarRow12326.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12326 ⟨27,by decide⟩ ∧
    (scalarRow12326.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12326 ⟨27,by decide⟩ + (scalarRow12326.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12326.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12326.targetFrame := by
  norm_num [cap12326, scalarRow12326, sourceIndex, cell12326, BstLean.Part263.envelope, parameters]

theorem repair12326Cell28 :
    0 ≤ cap12326 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12326 (parameters ⟨28,by decide⟩)
      (scalarRow12326.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12326 ⟨28,by decide⟩ ∧
    (scalarRow12326.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12326 ⟨28,by decide⟩ + (scalarRow12326.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12326.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12326.targetFrame := by
  norm_num [cap12326, scalarRow12326, sourceIndex, cell12326, BstLean.Part263.envelope, parameters]

theorem repair12326Cell29 :
    0 ≤ cap12326 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12326 (parameters ⟨29,by decide⟩)
      (scalarRow12326.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12326 ⟨29,by decide⟩ ∧
    (scalarRow12326.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12326 ⟨29,by decide⟩ + (scalarRow12326.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12326.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12326.targetFrame := by
  norm_num [cap12326, scalarRow12326, sourceIndex, cell12326, BstLean.Part263.envelope, parameters]

theorem repair12326Cell30 :
    0 ≤ cap12326 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12326 (parameters ⟨30,by decide⟩)
      (scalarRow12326.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12326 ⟨30,by decide⟩ ∧
    (scalarRow12326.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12326 ⟨30,by decide⟩ + (scalarRow12326.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12326.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12326.targetFrame := by
  norm_num [cap12326, scalarRow12326, sourceIndex, cell12326, BstLean.Part263.envelope, parameters]

theorem repair12326Cell31 :
    0 ≤ cap12326 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12326 (parameters ⟨31,by decide⟩)
      (scalarRow12326.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12326 ⟨31,by decide⟩ ∧
    (scalarRow12326.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12326 ⟨31,by decide⟩ + (scalarRow12326.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12326.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12326.targetFrame := by
  norm_num [cap12326, scalarRow12326, sourceIndex, cell12326, BstLean.Part263.envelope, parameters]

theorem repair12326Cell32 :
    0 ≤ cap12326 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12326 (parameters ⟨32,by decide⟩)
      (scalarRow12326.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12326 ⟨32,by decide⟩ ∧
    (scalarRow12326.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12326 ⟨32,by decide⟩ + (scalarRow12326.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12326.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12326.targetFrame := by
  norm_num [cap12326, scalarRow12326, sourceIndex, cell12326, BstLean.Part263.envelope, parameters]

theorem repair12326Cell33 :
    0 ≤ cap12326 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12326 (parameters ⟨33,by decide⟩)
      (scalarRow12326.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12326 ⟨33,by decide⟩ ∧
    (scalarRow12326.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12326 ⟨33,by decide⟩ + (scalarRow12326.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12326.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12326.targetFrame := by
  norm_num [cap12326, scalarRow12326, sourceIndex, cell12326, BstLean.Part263.envelope, parameters]

theorem repair12326Cell34 :
    0 ≤ cap12326 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12326 (parameters ⟨34,by decide⟩)
      (scalarRow12326.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12326 ⟨34,by decide⟩ ∧
    (scalarRow12326.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12326 ⟨34,by decide⟩ + (scalarRow12326.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12326.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12326.targetFrame := by
  norm_num [cap12326, scalarRow12326, sourceIndex, cell12326, BstLean.Part263.envelope, parameters]

theorem repair12326Cell35 :
    0 ≤ cap12326 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12326 (parameters ⟨35,by decide⟩)
      (scalarRow12326.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12326 ⟨35,by decide⟩ ∧
    (scalarRow12326.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12326 ⟨35,by decide⟩ + (scalarRow12326.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12326.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12326.targetFrame := by
  norm_num [cap12326, scalarRow12326, sourceIndex, cell12326, BstLean.Part263.envelope, parameters]

theorem repair12326Cell36 :
    0 ≤ cap12326 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12326 (parameters ⟨36,by decide⟩)
      (scalarRow12326.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12326 ⟨36,by decide⟩ ∧
    (scalarRow12326.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12326 ⟨36,by decide⟩ + (scalarRow12326.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12326.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12326.targetFrame := by
  norm_num [cap12326, scalarRow12326, sourceIndex, cell12326, BstLean.Part263.envelope, parameters]

theorem repair12326Cell37 :
    0 ≤ cap12326 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12326 (parameters ⟨37,by decide⟩)
      (scalarRow12326.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12326 ⟨37,by decide⟩ ∧
    (scalarRow12326.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12326 ⟨37,by decide⟩ + (scalarRow12326.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12326.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12326.targetFrame := by
  norm_num [cap12326, scalarRow12326, sourceIndex, cell12326, BstLean.Part263.envelope, parameters]

theorem repair12326Cell38 :
    0 ≤ cap12326 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12326 (parameters ⟨38,by decide⟩)
      (scalarRow12326.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12326 ⟨38,by decide⟩ ∧
    (scalarRow12326.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12326 ⟨38,by decide⟩ + (scalarRow12326.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12326.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12326.targetFrame := by
  norm_num [cap12326, scalarRow12326, sourceIndex, cell12326, BstLean.Part263.envelope, parameters]

theorem repair12326Cell39 :
    0 ≤ cap12326 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12326 (parameters ⟨39,by decide⟩)
      (scalarRow12326.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12326 ⟨39,by decide⟩ ∧
    (scalarRow12326.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12326 ⟨39,by decide⟩ + (scalarRow12326.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12326.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12326.targetFrame := by
  norm_num [cap12326, scalarRow12326, sourceIndex, cell12326, BstLean.Part263.envelope, parameters]

theorem repair12326Cell40 :
    0 ≤ cap12326 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12326 (parameters ⟨40,by decide⟩)
      (scalarRow12326.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12326 ⟨40,by decide⟩ ∧
    (scalarRow12326.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12326 ⟨40,by decide⟩ + (scalarRow12326.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12326.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12326.targetFrame := by
  norm_num [cap12326, scalarRow12326, sourceIndex, cell12326, BstLean.Part263.envelope, parameters]

theorem repair12326Cell41 :
    0 ≤ cap12326 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12326 (parameters ⟨41,by decide⟩)
      (scalarRow12326.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12326 ⟨41,by decide⟩ ∧
    (scalarRow12326.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12326 ⟨41,by decide⟩ + (scalarRow12326.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12326.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12326.targetFrame := by
  norm_num [cap12326, scalarRow12326, sourceIndex, cell12326, BstLean.Part263.envelope, parameters]

theorem repair12326Cell42 :
    0 ≤ cap12326 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12326 (parameters ⟨42,by decide⟩)
      (scalarRow12326.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12326 ⟨42,by decide⟩ ∧
    (scalarRow12326.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12326 ⟨42,by decide⟩ + (scalarRow12326.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12326.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12326.targetFrame := by
  norm_num [cap12326, scalarRow12326, sourceIndex, cell12326, BstLean.Part263.envelope, parameters]

theorem repair12326Cells (j : Fin 43) :
    0 ≤ cap12326 j ∧
    BstLean.Part263.envelope 12326 (parameters j) (scalarRow12326.table (sourceIndex j)).upper ≤ cap12326 j ∧
    (scalarRow12326.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12326 j + (scalarRow12326.table (sourceIndex j)).centre) /
      (scalarRow12326.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12326.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12326Cell0
  | ⟨1,_⟩ => exact repair12326Cell1
  | ⟨2,_⟩ => exact repair12326Cell2
  | ⟨3,_⟩ => exact repair12326Cell3
  | ⟨4,_⟩ => exact repair12326Cell4
  | ⟨5,_⟩ => exact repair12326Cell5
  | ⟨6,_⟩ => exact repair12326Cell6
  | ⟨7,_⟩ => exact repair12326Cell7
  | ⟨8,_⟩ => exact repair12326Cell8
  | ⟨9,_⟩ => exact repair12326Cell9
  | ⟨10,_⟩ => exact repair12326Cell10
  | ⟨11,_⟩ => exact repair12326Cell11
  | ⟨12,_⟩ => exact repair12326Cell12
  | ⟨13,_⟩ => exact repair12326Cell13
  | ⟨14,_⟩ => exact repair12326Cell14
  | ⟨15,_⟩ => exact repair12326Cell15
  | ⟨16,_⟩ => exact repair12326Cell16
  | ⟨17,_⟩ => exact repair12326Cell17
  | ⟨18,_⟩ => exact repair12326Cell18
  | ⟨19,_⟩ => exact repair12326Cell19
  | ⟨20,_⟩ => exact repair12326Cell20
  | ⟨21,_⟩ => exact repair12326Cell21
  | ⟨22,_⟩ => exact repair12326Cell22
  | ⟨23,_⟩ => exact repair12326Cell23
  | ⟨24,_⟩ => exact repair12326Cell24
  | ⟨25,_⟩ => exact repair12326Cell25
  | ⟨26,_⟩ => exact repair12326Cell26
  | ⟨27,_⟩ => exact repair12326Cell27
  | ⟨28,_⟩ => exact repair12326Cell28
  | ⟨29,_⟩ => exact repair12326Cell29
  | ⟨30,_⟩ => exact repair12326Cell30
  | ⟨31,_⟩ => exact repair12326Cell31
  | ⟨32,_⟩ => exact repair12326Cell32
  | ⟨33,_⟩ => exact repair12326Cell33
  | ⟨34,_⟩ => exact repair12326Cell34
  | ⟨35,_⟩ => exact repair12326Cell35
  | ⟨36,_⟩ => exact repair12326Cell36
  | ⟨37,_⟩ => exact repair12326Cell37
  | ⟨38,_⟩ => exact repair12326Cell38
  | ⟨39,_⟩ => exact repair12326Cell39
  | ⟨40,_⟩ => exact repair12326Cell40
  | ⟨41,_⟩ => exact repair12326Cell41
  | ⟨42,_⟩ => exact repair12326Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12326 : FrameRepair 12326 scalarRow12326 where
  cap := cap12326
  cap_nonneg := fun j => (repair12326Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12326])
  endpoint := fun j => (repair12326Cells j).2.1
  endpoint_upper := fun j => (repair12326Cells j).2.2.1
  frame := fun j => (repair12326Cells j).2.2.2

noncomputable def cap12327 : Fin 43 → ℝ
  | ⟨0,_⟩ => (275945027 / 1000000000 : ℝ)
  | ⟨1,_⟩ => (276347637 / 1000000000 : ℝ)
  | ⟨2,_⟩ => (138374627 / 500000000 : ℝ)
  | ⟨3,_⟩ => (138574937 / 500000000 : ℝ)
  | ⟨4,_⟩ => (277549503 / 1000000000 : ℝ)
  | ⟨5,_⟩ => (17371759 / 62500000 : ℝ)
  | ⟨6,_⟩ => (69586331 / 250000000 : ℝ)
  | ⟨7,_⟩ => (139370999 / 500000000 : ℝ)
  | ⟨8,_⟩ => (279137697 / 1000000000 : ℝ)
  | ⟨9,_⟩ => (11181297 / 40000000 : ℝ)
  | ⟨10,_⟩ => (139963091 / 500000000 : ℝ)
  | ⟨11,_⟩ => (280318491 / 1000000000 : ℝ)
  | ⟨12,_⟩ => (280710323 / 1000000000 : ℝ)
  | ⟨13,_⟩ => (70275177 / 250000000 : ℝ)
  | ⟨14,_⟩ => (281491027 / 1000000000 : ℝ)
  | ⟨15,_⟩ => (140940123 / 500000000 : ℝ)
  | ⟨16,_⟩ => (282268523 / 1000000000 : ℝ)
  | ⟨17,_⟩ => (28265587 / 100000000 : ℝ)
  | ⟨18,_⟩ => (283042277 / 1000000000 : ℝ)
  | ⟨19,_⟩ => (283427757 / 1000000000 : ℝ)
  | ⟨20,_⟩ => (28381231 / 100000000 : ℝ)
  | ⟨21,_⟩ => (284195947 / 1000000000 : ℝ)
  | ⟨22,_⟩ => (14228933 / 50000000 : ℝ)
  | ⟨23,_⟩ => (284959963 / 1000000000 : ℝ)
  | ⟨24,_⟩ => (142670427 / 500000000 : ℝ)
  | ⟨25,_⟩ => (57144077 / 200000000 : ℝ)
  | ⟨26,_⟩ => (286099511 / 1000000000 : ℝ)
  | ⟨27,_⟩ => (143238619 / 500000000 : ℝ)
  | ⟨28,_⟩ => (28685407 / 100000000 : ℝ)
  | ⟨29,_⟩ => (143615003 / 500000000 : ℝ)
  | ⟨30,_⟩ => (287604549 / 1000000000 : ℝ)
  | ⟨31,_⟩ => (71994677 / 250000000 : ℝ)
  | ⟨32,_⟩ => (288351987 / 1000000000 : ℝ)
  | ⟨33,_⟩ => (72180969 / 250000000 : ℝ)
  | ⟨34,_⟩ => (28909489 / 100000000 : ℝ)
  | ⟨35,_⟩ => (289465033 / 1000000000 : ℝ)
  | ⟨36,_⟩ => (2898343 / 10000000 : ℝ)
  | ⟨37,_⟩ => (72550677 / 250000000 : ℝ)
  | ⟨38,_⟩ => (290570251 / 1000000000 : ℝ)
  | ⟨39,_⟩ => (145468211 / 500000000 : ℝ)
  | ⟨40,_⟩ => (58260347 / 200000000 : ℝ)
  | ⟨41,_⟩ => (291666197 / 1000000000 : ℝ)
  | ⟨42,_⟩ => (292029807 / 1000000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12327Cell0 :
    0 ≤ cap12327 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12327 (parameters ⟨0,by decide⟩)
      (scalarRow12327.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12327 ⟨0,by decide⟩ ∧
    (scalarRow12327.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12327 ⟨0,by decide⟩ + (scalarRow12327.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12327.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12327.targetFrame := by
  norm_num [cap12327, scalarRow12327, sourceIndex, cell12327, BstLean.Part263.envelope, parameters]

theorem repair12327Cell1 :
    0 ≤ cap12327 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12327 (parameters ⟨1,by decide⟩)
      (scalarRow12327.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12327 ⟨1,by decide⟩ ∧
    (scalarRow12327.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12327 ⟨1,by decide⟩ + (scalarRow12327.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12327.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12327.targetFrame := by
  norm_num [cap12327, scalarRow12327, sourceIndex, cell12327, BstLean.Part263.envelope, parameters]

theorem repair12327Cell2 :
    0 ≤ cap12327 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12327 (parameters ⟨2,by decide⟩)
      (scalarRow12327.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12327 ⟨2,by decide⟩ ∧
    (scalarRow12327.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12327 ⟨2,by decide⟩ + (scalarRow12327.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12327.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12327.targetFrame := by
  norm_num [cap12327, scalarRow12327, sourceIndex, cell12327, BstLean.Part263.envelope, parameters]

theorem repair12327Cell3 :
    0 ≤ cap12327 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12327 (parameters ⟨3,by decide⟩)
      (scalarRow12327.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12327 ⟨3,by decide⟩ ∧
    (scalarRow12327.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12327 ⟨3,by decide⟩ + (scalarRow12327.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12327.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12327.targetFrame := by
  norm_num [cap12327, scalarRow12327, sourceIndex, cell12327, BstLean.Part263.envelope, parameters]

theorem repair12327Cell4 :
    0 ≤ cap12327 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12327 (parameters ⟨4,by decide⟩)
      (scalarRow12327.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12327 ⟨4,by decide⟩ ∧
    (scalarRow12327.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12327 ⟨4,by decide⟩ + (scalarRow12327.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12327.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12327.targetFrame := by
  norm_num [cap12327, scalarRow12327, sourceIndex, cell12327, BstLean.Part263.envelope, parameters]

theorem repair12327Cell5 :
    0 ≤ cap12327 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12327 (parameters ⟨5,by decide⟩)
      (scalarRow12327.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12327 ⟨5,by decide⟩ ∧
    (scalarRow12327.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12327 ⟨5,by decide⟩ + (scalarRow12327.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12327.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12327.targetFrame := by
  norm_num [cap12327, scalarRow12327, sourceIndex, cell12327, BstLean.Part263.envelope, parameters]

theorem repair12327Cell6 :
    0 ≤ cap12327 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12327 (parameters ⟨6,by decide⟩)
      (scalarRow12327.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12327 ⟨6,by decide⟩ ∧
    (scalarRow12327.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12327 ⟨6,by decide⟩ + (scalarRow12327.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12327.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12327.targetFrame := by
  norm_num [cap12327, scalarRow12327, sourceIndex, cell12327, BstLean.Part263.envelope, parameters]

theorem repair12327Cell7 :
    0 ≤ cap12327 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12327 (parameters ⟨7,by decide⟩)
      (scalarRow12327.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12327 ⟨7,by decide⟩ ∧
    (scalarRow12327.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12327 ⟨7,by decide⟩ + (scalarRow12327.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12327.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12327.targetFrame := by
  norm_num [cap12327, scalarRow12327, sourceIndex, cell12327, BstLean.Part263.envelope, parameters]

theorem repair12327Cell8 :
    0 ≤ cap12327 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12327 (parameters ⟨8,by decide⟩)
      (scalarRow12327.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12327 ⟨8,by decide⟩ ∧
    (scalarRow12327.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12327 ⟨8,by decide⟩ + (scalarRow12327.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12327.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12327.targetFrame := by
  norm_num [cap12327, scalarRow12327, sourceIndex, cell12327, BstLean.Part263.envelope, parameters]

theorem repair12327Cell9 :
    0 ≤ cap12327 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12327 (parameters ⟨9,by decide⟩)
      (scalarRow12327.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12327 ⟨9,by decide⟩ ∧
    (scalarRow12327.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12327 ⟨9,by decide⟩ + (scalarRow12327.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12327.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12327.targetFrame := by
  norm_num [cap12327, scalarRow12327, sourceIndex, cell12327, BstLean.Part263.envelope, parameters]

theorem repair12327Cell10 :
    0 ≤ cap12327 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12327 (parameters ⟨10,by decide⟩)
      (scalarRow12327.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12327 ⟨10,by decide⟩ ∧
    (scalarRow12327.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12327 ⟨10,by decide⟩ + (scalarRow12327.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12327.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12327.targetFrame := by
  norm_num [cap12327, scalarRow12327, sourceIndex, cell12327, BstLean.Part263.envelope, parameters]

theorem repair12327Cell11 :
    0 ≤ cap12327 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12327 (parameters ⟨11,by decide⟩)
      (scalarRow12327.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12327 ⟨11,by decide⟩ ∧
    (scalarRow12327.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12327 ⟨11,by decide⟩ + (scalarRow12327.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12327.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12327.targetFrame := by
  norm_num [cap12327, scalarRow12327, sourceIndex, cell12327, BstLean.Part263.envelope, parameters]

theorem repair12327Cell12 :
    0 ≤ cap12327 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12327 (parameters ⟨12,by decide⟩)
      (scalarRow12327.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12327 ⟨12,by decide⟩ ∧
    (scalarRow12327.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12327 ⟨12,by decide⟩ + (scalarRow12327.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12327.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12327.targetFrame := by
  norm_num [cap12327, scalarRow12327, sourceIndex, cell12327, BstLean.Part263.envelope, parameters]

theorem repair12327Cell13 :
    0 ≤ cap12327 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12327 (parameters ⟨13,by decide⟩)
      (scalarRow12327.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12327 ⟨13,by decide⟩ ∧
    (scalarRow12327.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12327 ⟨13,by decide⟩ + (scalarRow12327.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12327.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12327.targetFrame := by
  norm_num [cap12327, scalarRow12327, sourceIndex, cell12327, BstLean.Part263.envelope, parameters]

theorem repair12327Cell14 :
    0 ≤ cap12327 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12327 (parameters ⟨14,by decide⟩)
      (scalarRow12327.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12327 ⟨14,by decide⟩ ∧
    (scalarRow12327.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12327 ⟨14,by decide⟩ + (scalarRow12327.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12327.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12327.targetFrame := by
  norm_num [cap12327, scalarRow12327, sourceIndex, cell12327, BstLean.Part263.envelope, parameters]

theorem repair12327Cell15 :
    0 ≤ cap12327 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12327 (parameters ⟨15,by decide⟩)
      (scalarRow12327.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12327 ⟨15,by decide⟩ ∧
    (scalarRow12327.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12327 ⟨15,by decide⟩ + (scalarRow12327.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12327.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12327.targetFrame := by
  norm_num [cap12327, scalarRow12327, sourceIndex, cell12327, BstLean.Part263.envelope, parameters]

theorem repair12327Cell16 :
    0 ≤ cap12327 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12327 (parameters ⟨16,by decide⟩)
      (scalarRow12327.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12327 ⟨16,by decide⟩ ∧
    (scalarRow12327.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12327 ⟨16,by decide⟩ + (scalarRow12327.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12327.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12327.targetFrame := by
  norm_num [cap12327, scalarRow12327, sourceIndex, cell12327, BstLean.Part263.envelope, parameters]

theorem repair12327Cell17 :
    0 ≤ cap12327 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12327 (parameters ⟨17,by decide⟩)
      (scalarRow12327.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12327 ⟨17,by decide⟩ ∧
    (scalarRow12327.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12327 ⟨17,by decide⟩ + (scalarRow12327.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12327.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12327.targetFrame := by
  norm_num [cap12327, scalarRow12327, sourceIndex, cell12327, BstLean.Part263.envelope, parameters]

theorem repair12327Cell18 :
    0 ≤ cap12327 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12327 (parameters ⟨18,by decide⟩)
      (scalarRow12327.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12327 ⟨18,by decide⟩ ∧
    (scalarRow12327.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12327 ⟨18,by decide⟩ + (scalarRow12327.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12327.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12327.targetFrame := by
  norm_num [cap12327, scalarRow12327, sourceIndex, cell12327, BstLean.Part263.envelope, parameters]

theorem repair12327Cell19 :
    0 ≤ cap12327 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12327 (parameters ⟨19,by decide⟩)
      (scalarRow12327.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12327 ⟨19,by decide⟩ ∧
    (scalarRow12327.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12327 ⟨19,by decide⟩ + (scalarRow12327.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12327.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12327.targetFrame := by
  norm_num [cap12327, scalarRow12327, sourceIndex, cell12327, BstLean.Part263.envelope, parameters]

theorem repair12327Cell20 :
    0 ≤ cap12327 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12327 (parameters ⟨20,by decide⟩)
      (scalarRow12327.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12327 ⟨20,by decide⟩ ∧
    (scalarRow12327.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12327 ⟨20,by decide⟩ + (scalarRow12327.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12327.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12327.targetFrame := by
  norm_num [cap12327, scalarRow12327, sourceIndex, cell12327, BstLean.Part263.envelope, parameters]

theorem repair12327Cell21 :
    0 ≤ cap12327 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12327 (parameters ⟨21,by decide⟩)
      (scalarRow12327.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12327 ⟨21,by decide⟩ ∧
    (scalarRow12327.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12327 ⟨21,by decide⟩ + (scalarRow12327.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12327.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12327.targetFrame := by
  norm_num [cap12327, scalarRow12327, sourceIndex, cell12327, BstLean.Part263.envelope, parameters]

theorem repair12327Cell22 :
    0 ≤ cap12327 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12327 (parameters ⟨22,by decide⟩)
      (scalarRow12327.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12327 ⟨22,by decide⟩ ∧
    (scalarRow12327.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12327 ⟨22,by decide⟩ + (scalarRow12327.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12327.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12327.targetFrame := by
  norm_num [cap12327, scalarRow12327, sourceIndex, cell12327, BstLean.Part263.envelope, parameters]

theorem repair12327Cell23 :
    0 ≤ cap12327 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12327 (parameters ⟨23,by decide⟩)
      (scalarRow12327.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12327 ⟨23,by decide⟩ ∧
    (scalarRow12327.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12327 ⟨23,by decide⟩ + (scalarRow12327.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12327.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12327.targetFrame := by
  norm_num [cap12327, scalarRow12327, sourceIndex, cell12327, BstLean.Part263.envelope, parameters]

theorem repair12327Cell24 :
    0 ≤ cap12327 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12327 (parameters ⟨24,by decide⟩)
      (scalarRow12327.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12327 ⟨24,by decide⟩ ∧
    (scalarRow12327.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12327 ⟨24,by decide⟩ + (scalarRow12327.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12327.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12327.targetFrame := by
  norm_num [cap12327, scalarRow12327, sourceIndex, cell12327, BstLean.Part263.envelope, parameters]

theorem repair12327Cell25 :
    0 ≤ cap12327 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12327 (parameters ⟨25,by decide⟩)
      (scalarRow12327.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12327 ⟨25,by decide⟩ ∧
    (scalarRow12327.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12327 ⟨25,by decide⟩ + (scalarRow12327.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12327.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12327.targetFrame := by
  norm_num [cap12327, scalarRow12327, sourceIndex, cell12327, BstLean.Part263.envelope, parameters]

theorem repair12327Cell26 :
    0 ≤ cap12327 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12327 (parameters ⟨26,by decide⟩)
      (scalarRow12327.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12327 ⟨26,by decide⟩ ∧
    (scalarRow12327.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12327 ⟨26,by decide⟩ + (scalarRow12327.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12327.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12327.targetFrame := by
  norm_num [cap12327, scalarRow12327, sourceIndex, cell12327, BstLean.Part263.envelope, parameters]

theorem repair12327Cell27 :
    0 ≤ cap12327 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12327 (parameters ⟨27,by decide⟩)
      (scalarRow12327.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12327 ⟨27,by decide⟩ ∧
    (scalarRow12327.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12327 ⟨27,by decide⟩ + (scalarRow12327.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12327.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12327.targetFrame := by
  norm_num [cap12327, scalarRow12327, sourceIndex, cell12327, BstLean.Part263.envelope, parameters]

theorem repair12327Cell28 :
    0 ≤ cap12327 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12327 (parameters ⟨28,by decide⟩)
      (scalarRow12327.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12327 ⟨28,by decide⟩ ∧
    (scalarRow12327.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12327 ⟨28,by decide⟩ + (scalarRow12327.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12327.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12327.targetFrame := by
  norm_num [cap12327, scalarRow12327, sourceIndex, cell12327, BstLean.Part263.envelope, parameters]

theorem repair12327Cell29 :
    0 ≤ cap12327 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12327 (parameters ⟨29,by decide⟩)
      (scalarRow12327.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12327 ⟨29,by decide⟩ ∧
    (scalarRow12327.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12327 ⟨29,by decide⟩ + (scalarRow12327.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12327.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12327.targetFrame := by
  norm_num [cap12327, scalarRow12327, sourceIndex, cell12327, BstLean.Part263.envelope, parameters]

theorem repair12327Cell30 :
    0 ≤ cap12327 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12327 (parameters ⟨30,by decide⟩)
      (scalarRow12327.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12327 ⟨30,by decide⟩ ∧
    (scalarRow12327.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12327 ⟨30,by decide⟩ + (scalarRow12327.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12327.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12327.targetFrame := by
  norm_num [cap12327, scalarRow12327, sourceIndex, cell12327, BstLean.Part263.envelope, parameters]

theorem repair12327Cell31 :
    0 ≤ cap12327 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12327 (parameters ⟨31,by decide⟩)
      (scalarRow12327.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12327 ⟨31,by decide⟩ ∧
    (scalarRow12327.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12327 ⟨31,by decide⟩ + (scalarRow12327.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12327.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12327.targetFrame := by
  norm_num [cap12327, scalarRow12327, sourceIndex, cell12327, BstLean.Part263.envelope, parameters]

theorem repair12327Cell32 :
    0 ≤ cap12327 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12327 (parameters ⟨32,by decide⟩)
      (scalarRow12327.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12327 ⟨32,by decide⟩ ∧
    (scalarRow12327.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12327 ⟨32,by decide⟩ + (scalarRow12327.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12327.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12327.targetFrame := by
  norm_num [cap12327, scalarRow12327, sourceIndex, cell12327, BstLean.Part263.envelope, parameters]

theorem repair12327Cell33 :
    0 ≤ cap12327 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12327 (parameters ⟨33,by decide⟩)
      (scalarRow12327.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12327 ⟨33,by decide⟩ ∧
    (scalarRow12327.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12327 ⟨33,by decide⟩ + (scalarRow12327.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12327.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12327.targetFrame := by
  norm_num [cap12327, scalarRow12327, sourceIndex, cell12327, BstLean.Part263.envelope, parameters]

theorem repair12327Cell34 :
    0 ≤ cap12327 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12327 (parameters ⟨34,by decide⟩)
      (scalarRow12327.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12327 ⟨34,by decide⟩ ∧
    (scalarRow12327.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12327 ⟨34,by decide⟩ + (scalarRow12327.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12327.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12327.targetFrame := by
  norm_num [cap12327, scalarRow12327, sourceIndex, cell12327, BstLean.Part263.envelope, parameters]

theorem repair12327Cell35 :
    0 ≤ cap12327 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12327 (parameters ⟨35,by decide⟩)
      (scalarRow12327.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12327 ⟨35,by decide⟩ ∧
    (scalarRow12327.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12327 ⟨35,by decide⟩ + (scalarRow12327.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12327.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12327.targetFrame := by
  norm_num [cap12327, scalarRow12327, sourceIndex, cell12327, BstLean.Part263.envelope, parameters]

theorem repair12327Cell36 :
    0 ≤ cap12327 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12327 (parameters ⟨36,by decide⟩)
      (scalarRow12327.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12327 ⟨36,by decide⟩ ∧
    (scalarRow12327.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12327 ⟨36,by decide⟩ + (scalarRow12327.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12327.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12327.targetFrame := by
  norm_num [cap12327, scalarRow12327, sourceIndex, cell12327, BstLean.Part263.envelope, parameters]

theorem repair12327Cell37 :
    0 ≤ cap12327 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12327 (parameters ⟨37,by decide⟩)
      (scalarRow12327.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12327 ⟨37,by decide⟩ ∧
    (scalarRow12327.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12327 ⟨37,by decide⟩ + (scalarRow12327.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12327.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12327.targetFrame := by
  norm_num [cap12327, scalarRow12327, sourceIndex, cell12327, BstLean.Part263.envelope, parameters]

theorem repair12327Cell38 :
    0 ≤ cap12327 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12327 (parameters ⟨38,by decide⟩)
      (scalarRow12327.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12327 ⟨38,by decide⟩ ∧
    (scalarRow12327.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12327 ⟨38,by decide⟩ + (scalarRow12327.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12327.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12327.targetFrame := by
  norm_num [cap12327, scalarRow12327, sourceIndex, cell12327, BstLean.Part263.envelope, parameters]

theorem repair12327Cell39 :
    0 ≤ cap12327 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12327 (parameters ⟨39,by decide⟩)
      (scalarRow12327.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12327 ⟨39,by decide⟩ ∧
    (scalarRow12327.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12327 ⟨39,by decide⟩ + (scalarRow12327.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12327.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12327.targetFrame := by
  norm_num [cap12327, scalarRow12327, sourceIndex, cell12327, BstLean.Part263.envelope, parameters]

theorem repair12327Cell40 :
    0 ≤ cap12327 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12327 (parameters ⟨40,by decide⟩)
      (scalarRow12327.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12327 ⟨40,by decide⟩ ∧
    (scalarRow12327.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12327 ⟨40,by decide⟩ + (scalarRow12327.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12327.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12327.targetFrame := by
  norm_num [cap12327, scalarRow12327, sourceIndex, cell12327, BstLean.Part263.envelope, parameters]

theorem repair12327Cell41 :
    0 ≤ cap12327 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12327 (parameters ⟨41,by decide⟩)
      (scalarRow12327.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12327 ⟨41,by decide⟩ ∧
    (scalarRow12327.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12327 ⟨41,by decide⟩ + (scalarRow12327.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12327.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12327.targetFrame := by
  norm_num [cap12327, scalarRow12327, sourceIndex, cell12327, BstLean.Part263.envelope, parameters]

theorem repair12327Cell42 :
    0 ≤ cap12327 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12327 (parameters ⟨42,by decide⟩)
      (scalarRow12327.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12327 ⟨42,by decide⟩ ∧
    (scalarRow12327.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12327 ⟨42,by decide⟩ + (scalarRow12327.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12327.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12327.targetFrame := by
  norm_num [cap12327, scalarRow12327, sourceIndex, cell12327, BstLean.Part263.envelope, parameters]

theorem repair12327Cells (j : Fin 43) :
    0 ≤ cap12327 j ∧
    BstLean.Part263.envelope 12327 (parameters j) (scalarRow12327.table (sourceIndex j)).upper ≤ cap12327 j ∧
    (scalarRow12327.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12327 j + (scalarRow12327.table (sourceIndex j)).centre) /
      (scalarRow12327.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12327.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12327Cell0
  | ⟨1,_⟩ => exact repair12327Cell1
  | ⟨2,_⟩ => exact repair12327Cell2
  | ⟨3,_⟩ => exact repair12327Cell3
  | ⟨4,_⟩ => exact repair12327Cell4
  | ⟨5,_⟩ => exact repair12327Cell5
  | ⟨6,_⟩ => exact repair12327Cell6
  | ⟨7,_⟩ => exact repair12327Cell7
  | ⟨8,_⟩ => exact repair12327Cell8
  | ⟨9,_⟩ => exact repair12327Cell9
  | ⟨10,_⟩ => exact repair12327Cell10
  | ⟨11,_⟩ => exact repair12327Cell11
  | ⟨12,_⟩ => exact repair12327Cell12
  | ⟨13,_⟩ => exact repair12327Cell13
  | ⟨14,_⟩ => exact repair12327Cell14
  | ⟨15,_⟩ => exact repair12327Cell15
  | ⟨16,_⟩ => exact repair12327Cell16
  | ⟨17,_⟩ => exact repair12327Cell17
  | ⟨18,_⟩ => exact repair12327Cell18
  | ⟨19,_⟩ => exact repair12327Cell19
  | ⟨20,_⟩ => exact repair12327Cell20
  | ⟨21,_⟩ => exact repair12327Cell21
  | ⟨22,_⟩ => exact repair12327Cell22
  | ⟨23,_⟩ => exact repair12327Cell23
  | ⟨24,_⟩ => exact repair12327Cell24
  | ⟨25,_⟩ => exact repair12327Cell25
  | ⟨26,_⟩ => exact repair12327Cell26
  | ⟨27,_⟩ => exact repair12327Cell27
  | ⟨28,_⟩ => exact repair12327Cell28
  | ⟨29,_⟩ => exact repair12327Cell29
  | ⟨30,_⟩ => exact repair12327Cell30
  | ⟨31,_⟩ => exact repair12327Cell31
  | ⟨32,_⟩ => exact repair12327Cell32
  | ⟨33,_⟩ => exact repair12327Cell33
  | ⟨34,_⟩ => exact repair12327Cell34
  | ⟨35,_⟩ => exact repair12327Cell35
  | ⟨36,_⟩ => exact repair12327Cell36
  | ⟨37,_⟩ => exact repair12327Cell37
  | ⟨38,_⟩ => exact repair12327Cell38
  | ⟨39,_⟩ => exact repair12327Cell39
  | ⟨40,_⟩ => exact repair12327Cell40
  | ⟨41,_⟩ => exact repair12327Cell41
  | ⟨42,_⟩ => exact repair12327Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12327 : FrameRepair 12327 scalarRow12327 where
  cap := cap12327
  cap_nonneg := fun j => (repair12327Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12327])
  endpoint := fun j => (repair12327Cells j).2.1
  endpoint_upper := fun j => (repair12327Cells j).2.2.1
  frame := fun j => (repair12327Cells j).2.2.2

noncomputable def cap12328 : Fin 43 → ℝ
  | ⟨0,_⟩ => (34493119 / 125000000 : ℝ)
  | ⟨1,_⟩ => (69086889 / 250000000 : ℝ)
  | ⟨2,_⟩ => (138374583 / 500000000 : ℝ)
  | ⟨3,_⟩ => (277149779 / 1000000000 : ℝ)
  | ⟨4,_⟩ => (277549403 / 1000000000 : ℝ)
  | ⟨5,_⟩ => (277948037 / 1000000000 : ℝ)
  | ⟨6,_⟩ => (27834521 / 100000000 : ℝ)
  | ⟨7,_⟩ => (139370939 / 500000000 : ℝ)
  | ⟨8,_⟩ => (279137571 / 1000000000 : ℝ)
  | ⟨9,_⟩ => (69883073 / 250000000 : ℝ)
  | ⟨10,_⟩ => (279926043 / 1000000000 : ℝ)
  | ⟨11,_⟩ => (56063669 / 200000000 : ℝ)
  | ⟨12,_⟩ => (280710171 / 1000000000 : ℝ)
  | ⟨13,_⟩ => (5622011 / 20000000 : ℝ)
  | ⟨14,_⟩ => (281490863 / 1000000000 : ℝ)
  | ⟨15,_⟩ => (70470019 / 250000000 : ℝ)
  | ⟨16,_⟩ => (282268347 / 1000000000 : ℝ)
  | ⟨17,_⟩ => (282655687 / 1000000000 : ℝ)
  | ⟨18,_⟩ => (35380261 / 125000000 : ℝ)
  | ⟨19,_⟩ => (141713781 / 500000000 : ℝ)
  | ⟨20,_⟩ => (70953027 / 250000000 : ℝ)
  | ⟨21,_⟩ => (284195739 / 1000000000 : ℝ)
  | ⟨22,_⟩ => (142289223 / 500000000 : ℝ)
  | ⟨23,_⟩ => (284959743 / 1000000000 : ℝ)
  | ⟨24,_⟩ => (71335157 / 250000000 : ℝ)
  | ⟨25,_⟩ => (35715019 / 125000000 : ℝ)
  | ⟨26,_⟩ => (286099273 / 1000000000 : ℝ)
  | ⟨27,_⟩ => (143238497 / 500000000 : ℝ)
  | ⟨28,_⟩ => (286853819 / 1000000000 : ℝ)
  | ⟨29,_⟩ => (287229749 / 1000000000 : ℝ)
  | ⟨30,_⟩ => (143802143 / 500000000 : ℝ)
  | ⟨31,_⟩ => (287978439 / 1000000000 : ℝ)
  | ⟨32,_⟩ => (9010991 / 31250000 : ℝ)
  | ⟨33,_⟩ => (57744719 / 200000000 : ℝ)
  | ⟨34,_⟩ => (289094603 / 1000000000 : ℝ)
  | ⟨35,_⟩ => (14473237 / 50000000 : ℝ)
  | ⟨36,_⟩ => (289834001 / 1000000000 : ℝ)
  | ⟨37,_⟩ => (290202403 / 1000000000 : ℝ)
  | ⟨38,_⟩ => (14528497 / 50000000 : ℝ)
  | ⟨39,_⟩ => (145468053 / 500000000 : ℝ)
  | ⟨40,_⟩ => (291301413 / 1000000000 : ℝ)
  | ⟨41,_⟩ => (72916467 / 250000000 : ℝ)
  | ⟨42,_⟩ => (292029473 / 1000000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12328Cell0 :
    0 ≤ cap12328 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12328 (parameters ⟨0,by decide⟩)
      (scalarRow12328.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12328 ⟨0,by decide⟩ ∧
    (scalarRow12328.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12328 ⟨0,by decide⟩ + (scalarRow12328.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12328.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12328.targetFrame := by
  norm_num [cap12328, scalarRow12328, sourceIndex, cell12328, BstLean.Part263.envelope, parameters]

theorem repair12328Cell1 :
    0 ≤ cap12328 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12328 (parameters ⟨1,by decide⟩)
      (scalarRow12328.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12328 ⟨1,by decide⟩ ∧
    (scalarRow12328.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12328 ⟨1,by decide⟩ + (scalarRow12328.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12328.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12328.targetFrame := by
  norm_num [cap12328, scalarRow12328, sourceIndex, cell12328, BstLean.Part263.envelope, parameters]

theorem repair12328Cell2 :
    0 ≤ cap12328 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12328 (parameters ⟨2,by decide⟩)
      (scalarRow12328.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12328 ⟨2,by decide⟩ ∧
    (scalarRow12328.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12328 ⟨2,by decide⟩ + (scalarRow12328.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12328.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12328.targetFrame := by
  norm_num [cap12328, scalarRow12328, sourceIndex, cell12328, BstLean.Part263.envelope, parameters]

theorem repair12328Cell3 :
    0 ≤ cap12328 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12328 (parameters ⟨3,by decide⟩)
      (scalarRow12328.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12328 ⟨3,by decide⟩ ∧
    (scalarRow12328.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12328 ⟨3,by decide⟩ + (scalarRow12328.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12328.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12328.targetFrame := by
  norm_num [cap12328, scalarRow12328, sourceIndex, cell12328, BstLean.Part263.envelope, parameters]

theorem repair12328Cell4 :
    0 ≤ cap12328 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12328 (parameters ⟨4,by decide⟩)
      (scalarRow12328.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12328 ⟨4,by decide⟩ ∧
    (scalarRow12328.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12328 ⟨4,by decide⟩ + (scalarRow12328.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12328.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12328.targetFrame := by
  norm_num [cap12328, scalarRow12328, sourceIndex, cell12328, BstLean.Part263.envelope, parameters]

theorem repair12328Cell5 :
    0 ≤ cap12328 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12328 (parameters ⟨5,by decide⟩)
      (scalarRow12328.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12328 ⟨5,by decide⟩ ∧
    (scalarRow12328.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12328 ⟨5,by decide⟩ + (scalarRow12328.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12328.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12328.targetFrame := by
  norm_num [cap12328, scalarRow12328, sourceIndex, cell12328, BstLean.Part263.envelope, parameters]

theorem repair12328Cell6 :
    0 ≤ cap12328 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12328 (parameters ⟨6,by decide⟩)
      (scalarRow12328.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12328 ⟨6,by decide⟩ ∧
    (scalarRow12328.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12328 ⟨6,by decide⟩ + (scalarRow12328.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12328.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12328.targetFrame := by
  norm_num [cap12328, scalarRow12328, sourceIndex, cell12328, BstLean.Part263.envelope, parameters]

theorem repair12328Cell7 :
    0 ≤ cap12328 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12328 (parameters ⟨7,by decide⟩)
      (scalarRow12328.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12328 ⟨7,by decide⟩ ∧
    (scalarRow12328.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12328 ⟨7,by decide⟩ + (scalarRow12328.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12328.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12328.targetFrame := by
  norm_num [cap12328, scalarRow12328, sourceIndex, cell12328, BstLean.Part263.envelope, parameters]

theorem repair12328Cell8 :
    0 ≤ cap12328 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12328 (parameters ⟨8,by decide⟩)
      (scalarRow12328.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12328 ⟨8,by decide⟩ ∧
    (scalarRow12328.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12328 ⟨8,by decide⟩ + (scalarRow12328.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12328.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12328.targetFrame := by
  norm_num [cap12328, scalarRow12328, sourceIndex, cell12328, BstLean.Part263.envelope, parameters]

theorem repair12328Cell9 :
    0 ≤ cap12328 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12328 (parameters ⟨9,by decide⟩)
      (scalarRow12328.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12328 ⟨9,by decide⟩ ∧
    (scalarRow12328.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12328 ⟨9,by decide⟩ + (scalarRow12328.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12328.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12328.targetFrame := by
  norm_num [cap12328, scalarRow12328, sourceIndex, cell12328, BstLean.Part263.envelope, parameters]

theorem repair12328Cell10 :
    0 ≤ cap12328 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12328 (parameters ⟨10,by decide⟩)
      (scalarRow12328.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12328 ⟨10,by decide⟩ ∧
    (scalarRow12328.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12328 ⟨10,by decide⟩ + (scalarRow12328.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12328.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12328.targetFrame := by
  norm_num [cap12328, scalarRow12328, sourceIndex, cell12328, BstLean.Part263.envelope, parameters]

theorem repair12328Cell11 :
    0 ≤ cap12328 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12328 (parameters ⟨11,by decide⟩)
      (scalarRow12328.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12328 ⟨11,by decide⟩ ∧
    (scalarRow12328.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12328 ⟨11,by decide⟩ + (scalarRow12328.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12328.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12328.targetFrame := by
  norm_num [cap12328, scalarRow12328, sourceIndex, cell12328, BstLean.Part263.envelope, parameters]

theorem repair12328Cell12 :
    0 ≤ cap12328 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12328 (parameters ⟨12,by decide⟩)
      (scalarRow12328.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12328 ⟨12,by decide⟩ ∧
    (scalarRow12328.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12328 ⟨12,by decide⟩ + (scalarRow12328.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12328.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12328.targetFrame := by
  norm_num [cap12328, scalarRow12328, sourceIndex, cell12328, BstLean.Part263.envelope, parameters]

theorem repair12328Cell13 :
    0 ≤ cap12328 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12328 (parameters ⟨13,by decide⟩)
      (scalarRow12328.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12328 ⟨13,by decide⟩ ∧
    (scalarRow12328.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12328 ⟨13,by decide⟩ + (scalarRow12328.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12328.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12328.targetFrame := by
  norm_num [cap12328, scalarRow12328, sourceIndex, cell12328, BstLean.Part263.envelope, parameters]

theorem repair12328Cell14 :
    0 ≤ cap12328 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12328 (parameters ⟨14,by decide⟩)
      (scalarRow12328.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12328 ⟨14,by decide⟩ ∧
    (scalarRow12328.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12328 ⟨14,by decide⟩ + (scalarRow12328.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12328.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12328.targetFrame := by
  norm_num [cap12328, scalarRow12328, sourceIndex, cell12328, BstLean.Part263.envelope, parameters]

theorem repair12328Cell15 :
    0 ≤ cap12328 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12328 (parameters ⟨15,by decide⟩)
      (scalarRow12328.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12328 ⟨15,by decide⟩ ∧
    (scalarRow12328.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12328 ⟨15,by decide⟩ + (scalarRow12328.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12328.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12328.targetFrame := by
  norm_num [cap12328, scalarRow12328, sourceIndex, cell12328, BstLean.Part263.envelope, parameters]

theorem repair12328Cell16 :
    0 ≤ cap12328 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12328 (parameters ⟨16,by decide⟩)
      (scalarRow12328.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12328 ⟨16,by decide⟩ ∧
    (scalarRow12328.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12328 ⟨16,by decide⟩ + (scalarRow12328.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12328.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12328.targetFrame := by
  norm_num [cap12328, scalarRow12328, sourceIndex, cell12328, BstLean.Part263.envelope, parameters]

theorem repair12328Cell17 :
    0 ≤ cap12328 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12328 (parameters ⟨17,by decide⟩)
      (scalarRow12328.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12328 ⟨17,by decide⟩ ∧
    (scalarRow12328.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12328 ⟨17,by decide⟩ + (scalarRow12328.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12328.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12328.targetFrame := by
  norm_num [cap12328, scalarRow12328, sourceIndex, cell12328, BstLean.Part263.envelope, parameters]

theorem repair12328Cell18 :
    0 ≤ cap12328 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12328 (parameters ⟨18,by decide⟩)
      (scalarRow12328.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12328 ⟨18,by decide⟩ ∧
    (scalarRow12328.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12328 ⟨18,by decide⟩ + (scalarRow12328.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12328.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12328.targetFrame := by
  norm_num [cap12328, scalarRow12328, sourceIndex, cell12328, BstLean.Part263.envelope, parameters]

theorem repair12328Cell19 :
    0 ≤ cap12328 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12328 (parameters ⟨19,by decide⟩)
      (scalarRow12328.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12328 ⟨19,by decide⟩ ∧
    (scalarRow12328.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12328 ⟨19,by decide⟩ + (scalarRow12328.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12328.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12328.targetFrame := by
  norm_num [cap12328, scalarRow12328, sourceIndex, cell12328, BstLean.Part263.envelope, parameters]

theorem repair12328Cell20 :
    0 ≤ cap12328 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12328 (parameters ⟨20,by decide⟩)
      (scalarRow12328.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12328 ⟨20,by decide⟩ ∧
    (scalarRow12328.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12328 ⟨20,by decide⟩ + (scalarRow12328.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12328.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12328.targetFrame := by
  norm_num [cap12328, scalarRow12328, sourceIndex, cell12328, BstLean.Part263.envelope, parameters]

theorem repair12328Cell21 :
    0 ≤ cap12328 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12328 (parameters ⟨21,by decide⟩)
      (scalarRow12328.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12328 ⟨21,by decide⟩ ∧
    (scalarRow12328.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12328 ⟨21,by decide⟩ + (scalarRow12328.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12328.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12328.targetFrame := by
  norm_num [cap12328, scalarRow12328, sourceIndex, cell12328, BstLean.Part263.envelope, parameters]

theorem repair12328Cell22 :
    0 ≤ cap12328 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12328 (parameters ⟨22,by decide⟩)
      (scalarRow12328.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12328 ⟨22,by decide⟩ ∧
    (scalarRow12328.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12328 ⟨22,by decide⟩ + (scalarRow12328.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12328.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12328.targetFrame := by
  norm_num [cap12328, scalarRow12328, sourceIndex, cell12328, BstLean.Part263.envelope, parameters]

theorem repair12328Cell23 :
    0 ≤ cap12328 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12328 (parameters ⟨23,by decide⟩)
      (scalarRow12328.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12328 ⟨23,by decide⟩ ∧
    (scalarRow12328.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12328 ⟨23,by decide⟩ + (scalarRow12328.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12328.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12328.targetFrame := by
  norm_num [cap12328, scalarRow12328, sourceIndex, cell12328, BstLean.Part263.envelope, parameters]

theorem repair12328Cell24 :
    0 ≤ cap12328 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12328 (parameters ⟨24,by decide⟩)
      (scalarRow12328.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12328 ⟨24,by decide⟩ ∧
    (scalarRow12328.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12328 ⟨24,by decide⟩ + (scalarRow12328.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12328.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12328.targetFrame := by
  norm_num [cap12328, scalarRow12328, sourceIndex, cell12328, BstLean.Part263.envelope, parameters]

theorem repair12328Cell25 :
    0 ≤ cap12328 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12328 (parameters ⟨25,by decide⟩)
      (scalarRow12328.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12328 ⟨25,by decide⟩ ∧
    (scalarRow12328.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12328 ⟨25,by decide⟩ + (scalarRow12328.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12328.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12328.targetFrame := by
  norm_num [cap12328, scalarRow12328, sourceIndex, cell12328, BstLean.Part263.envelope, parameters]

theorem repair12328Cell26 :
    0 ≤ cap12328 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12328 (parameters ⟨26,by decide⟩)
      (scalarRow12328.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12328 ⟨26,by decide⟩ ∧
    (scalarRow12328.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12328 ⟨26,by decide⟩ + (scalarRow12328.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12328.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12328.targetFrame := by
  norm_num [cap12328, scalarRow12328, sourceIndex, cell12328, BstLean.Part263.envelope, parameters]

theorem repair12328Cell27 :
    0 ≤ cap12328 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12328 (parameters ⟨27,by decide⟩)
      (scalarRow12328.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12328 ⟨27,by decide⟩ ∧
    (scalarRow12328.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12328 ⟨27,by decide⟩ + (scalarRow12328.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12328.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12328.targetFrame := by
  norm_num [cap12328, scalarRow12328, sourceIndex, cell12328, BstLean.Part263.envelope, parameters]

theorem repair12328Cell28 :
    0 ≤ cap12328 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12328 (parameters ⟨28,by decide⟩)
      (scalarRow12328.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12328 ⟨28,by decide⟩ ∧
    (scalarRow12328.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12328 ⟨28,by decide⟩ + (scalarRow12328.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12328.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12328.targetFrame := by
  norm_num [cap12328, scalarRow12328, sourceIndex, cell12328, BstLean.Part263.envelope, parameters]

theorem repair12328Cell29 :
    0 ≤ cap12328 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12328 (parameters ⟨29,by decide⟩)
      (scalarRow12328.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12328 ⟨29,by decide⟩ ∧
    (scalarRow12328.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12328 ⟨29,by decide⟩ + (scalarRow12328.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12328.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12328.targetFrame := by
  norm_num [cap12328, scalarRow12328, sourceIndex, cell12328, BstLean.Part263.envelope, parameters]

theorem repair12328Cell30 :
    0 ≤ cap12328 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12328 (parameters ⟨30,by decide⟩)
      (scalarRow12328.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12328 ⟨30,by decide⟩ ∧
    (scalarRow12328.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12328 ⟨30,by decide⟩ + (scalarRow12328.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12328.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12328.targetFrame := by
  norm_num [cap12328, scalarRow12328, sourceIndex, cell12328, BstLean.Part263.envelope, parameters]

theorem repair12328Cell31 :
    0 ≤ cap12328 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12328 (parameters ⟨31,by decide⟩)
      (scalarRow12328.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12328 ⟨31,by decide⟩ ∧
    (scalarRow12328.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12328 ⟨31,by decide⟩ + (scalarRow12328.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12328.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12328.targetFrame := by
  norm_num [cap12328, scalarRow12328, sourceIndex, cell12328, BstLean.Part263.envelope, parameters]

theorem repair12328Cell32 :
    0 ≤ cap12328 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12328 (parameters ⟨32,by decide⟩)
      (scalarRow12328.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12328 ⟨32,by decide⟩ ∧
    (scalarRow12328.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12328 ⟨32,by decide⟩ + (scalarRow12328.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12328.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12328.targetFrame := by
  norm_num [cap12328, scalarRow12328, sourceIndex, cell12328, BstLean.Part263.envelope, parameters]

theorem repair12328Cell33 :
    0 ≤ cap12328 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12328 (parameters ⟨33,by decide⟩)
      (scalarRow12328.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12328 ⟨33,by decide⟩ ∧
    (scalarRow12328.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12328 ⟨33,by decide⟩ + (scalarRow12328.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12328.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12328.targetFrame := by
  norm_num [cap12328, scalarRow12328, sourceIndex, cell12328, BstLean.Part263.envelope, parameters]

theorem repair12328Cell34 :
    0 ≤ cap12328 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12328 (parameters ⟨34,by decide⟩)
      (scalarRow12328.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12328 ⟨34,by decide⟩ ∧
    (scalarRow12328.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12328 ⟨34,by decide⟩ + (scalarRow12328.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12328.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12328.targetFrame := by
  norm_num [cap12328, scalarRow12328, sourceIndex, cell12328, BstLean.Part263.envelope, parameters]

theorem repair12328Cell35 :
    0 ≤ cap12328 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12328 (parameters ⟨35,by decide⟩)
      (scalarRow12328.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12328 ⟨35,by decide⟩ ∧
    (scalarRow12328.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12328 ⟨35,by decide⟩ + (scalarRow12328.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12328.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12328.targetFrame := by
  norm_num [cap12328, scalarRow12328, sourceIndex, cell12328, BstLean.Part263.envelope, parameters]

theorem repair12328Cell36 :
    0 ≤ cap12328 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12328 (parameters ⟨36,by decide⟩)
      (scalarRow12328.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12328 ⟨36,by decide⟩ ∧
    (scalarRow12328.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12328 ⟨36,by decide⟩ + (scalarRow12328.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12328.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12328.targetFrame := by
  norm_num [cap12328, scalarRow12328, sourceIndex, cell12328, BstLean.Part263.envelope, parameters]

theorem repair12328Cell37 :
    0 ≤ cap12328 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12328 (parameters ⟨37,by decide⟩)
      (scalarRow12328.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12328 ⟨37,by decide⟩ ∧
    (scalarRow12328.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12328 ⟨37,by decide⟩ + (scalarRow12328.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12328.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12328.targetFrame := by
  norm_num [cap12328, scalarRow12328, sourceIndex, cell12328, BstLean.Part263.envelope, parameters]

theorem repair12328Cell38 :
    0 ≤ cap12328 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12328 (parameters ⟨38,by decide⟩)
      (scalarRow12328.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12328 ⟨38,by decide⟩ ∧
    (scalarRow12328.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12328 ⟨38,by decide⟩ + (scalarRow12328.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12328.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12328.targetFrame := by
  norm_num [cap12328, scalarRow12328, sourceIndex, cell12328, BstLean.Part263.envelope, parameters]

theorem repair12328Cell39 :
    0 ≤ cap12328 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12328 (parameters ⟨39,by decide⟩)
      (scalarRow12328.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12328 ⟨39,by decide⟩ ∧
    (scalarRow12328.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12328 ⟨39,by decide⟩ + (scalarRow12328.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12328.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12328.targetFrame := by
  norm_num [cap12328, scalarRow12328, sourceIndex, cell12328, BstLean.Part263.envelope, parameters]

theorem repair12328Cell40 :
    0 ≤ cap12328 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12328 (parameters ⟨40,by decide⟩)
      (scalarRow12328.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12328 ⟨40,by decide⟩ ∧
    (scalarRow12328.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12328 ⟨40,by decide⟩ + (scalarRow12328.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12328.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12328.targetFrame := by
  norm_num [cap12328, scalarRow12328, sourceIndex, cell12328, BstLean.Part263.envelope, parameters]

theorem repair12328Cell41 :
    0 ≤ cap12328 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12328 (parameters ⟨41,by decide⟩)
      (scalarRow12328.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12328 ⟨41,by decide⟩ ∧
    (scalarRow12328.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12328 ⟨41,by decide⟩ + (scalarRow12328.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12328.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12328.targetFrame := by
  norm_num [cap12328, scalarRow12328, sourceIndex, cell12328, BstLean.Part263.envelope, parameters]

theorem repair12328Cell42 :
    0 ≤ cap12328 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12328 (parameters ⟨42,by decide⟩)
      (scalarRow12328.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12328 ⟨42,by decide⟩ ∧
    (scalarRow12328.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12328 ⟨42,by decide⟩ + (scalarRow12328.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12328.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12328.targetFrame := by
  norm_num [cap12328, scalarRow12328, sourceIndex, cell12328, BstLean.Part263.envelope, parameters]

theorem repair12328Cells (j : Fin 43) :
    0 ≤ cap12328 j ∧
    BstLean.Part263.envelope 12328 (parameters j) (scalarRow12328.table (sourceIndex j)).upper ≤ cap12328 j ∧
    (scalarRow12328.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12328 j + (scalarRow12328.table (sourceIndex j)).centre) /
      (scalarRow12328.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12328.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12328Cell0
  | ⟨1,_⟩ => exact repair12328Cell1
  | ⟨2,_⟩ => exact repair12328Cell2
  | ⟨3,_⟩ => exact repair12328Cell3
  | ⟨4,_⟩ => exact repair12328Cell4
  | ⟨5,_⟩ => exact repair12328Cell5
  | ⟨6,_⟩ => exact repair12328Cell6
  | ⟨7,_⟩ => exact repair12328Cell7
  | ⟨8,_⟩ => exact repair12328Cell8
  | ⟨9,_⟩ => exact repair12328Cell9
  | ⟨10,_⟩ => exact repair12328Cell10
  | ⟨11,_⟩ => exact repair12328Cell11
  | ⟨12,_⟩ => exact repair12328Cell12
  | ⟨13,_⟩ => exact repair12328Cell13
  | ⟨14,_⟩ => exact repair12328Cell14
  | ⟨15,_⟩ => exact repair12328Cell15
  | ⟨16,_⟩ => exact repair12328Cell16
  | ⟨17,_⟩ => exact repair12328Cell17
  | ⟨18,_⟩ => exact repair12328Cell18
  | ⟨19,_⟩ => exact repair12328Cell19
  | ⟨20,_⟩ => exact repair12328Cell20
  | ⟨21,_⟩ => exact repair12328Cell21
  | ⟨22,_⟩ => exact repair12328Cell22
  | ⟨23,_⟩ => exact repair12328Cell23
  | ⟨24,_⟩ => exact repair12328Cell24
  | ⟨25,_⟩ => exact repair12328Cell25
  | ⟨26,_⟩ => exact repair12328Cell26
  | ⟨27,_⟩ => exact repair12328Cell27
  | ⟨28,_⟩ => exact repair12328Cell28
  | ⟨29,_⟩ => exact repair12328Cell29
  | ⟨30,_⟩ => exact repair12328Cell30
  | ⟨31,_⟩ => exact repair12328Cell31
  | ⟨32,_⟩ => exact repair12328Cell32
  | ⟨33,_⟩ => exact repair12328Cell33
  | ⟨34,_⟩ => exact repair12328Cell34
  | ⟨35,_⟩ => exact repair12328Cell35
  | ⟨36,_⟩ => exact repair12328Cell36
  | ⟨37,_⟩ => exact repair12328Cell37
  | ⟨38,_⟩ => exact repair12328Cell38
  | ⟨39,_⟩ => exact repair12328Cell39
  | ⟨40,_⟩ => exact repair12328Cell40
  | ⟨41,_⟩ => exact repair12328Cell41
  | ⟨42,_⟩ => exact repair12328Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12328 : FrameRepair 12328 scalarRow12328 where
  cap := cap12328
  cap_nonneg := fun j => (repair12328Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12328])
  endpoint := fun j => (repair12328Cells j).2.1
  endpoint_upper := fun j => (repair12328Cells j).2.2.1
  frame := fun j => (repair12328Cells j).2.2.2

noncomputable def cap12329 : Fin 43 → ℝ
  | ⟨0,_⟩ => (275944877 / 1000000000 : ℝ)
  | ⟨1,_⟩ => (138173737 / 500000000 : ℝ)
  | ⟨2,_⟩ => (138374539 / 500000000 : ℝ)
  | ⟨3,_⟩ => (55429937 / 200000000 : ℝ)
  | ⟨4,_⟩ => (138774651 / 500000000 : ℝ)
  | ⟨5,_⟩ => (27794793 / 100000000 : ℝ)
  | ⟨6,_⟩ => (278345097 / 1000000000 : ℝ)
  | ⟨7,_⟩ => (278741759 / 1000000000 : ℝ)
  | ⟨8,_⟩ => (55827489 / 200000000 : ℝ)
  | ⟨9,_⟩ => (436769 / 1562500 : ℝ)
  | ⟨10,_⟩ => (17495369 / 62500000 : ℝ)
  | ⟨11,_⟩ => (1401591 / 5000000 : ℝ)
  | ⟨12,_⟩ => (14035501 / 50000000 : ℝ)
  | ⟨13,_⟩ => (35137549 / 125000000 : ℝ)
  | ⟨14,_⟩ => (281490699 / 1000000000 : ℝ)
  | ⟨15,_⟩ => (140939953 / 500000000 : ℝ)
  | ⟨16,_⟩ => (28226817 / 100000000 : ℝ)
  | ⟨17,_⟩ => (17665969 / 62500000 : ℝ)
  | ⟨18,_⟩ => (283041899 / 1000000000 : ℝ)
  | ⟨19,_⟩ => (141713683 / 500000000 : ℝ)
  | ⟨20,_⟩ => (283811907 / 1000000000 : ℝ)
  | ⟨21,_⟩ => (284195531 / 1000000000 : ℝ)
  | ⟨22,_⟩ => (284578233 / 1000000000 : ℝ)
  | ⟨23,_⟩ => (284959523 / 1000000000 : ℝ)
  | ⟨24,_⟩ => (142670201 / 500000000 : ℝ)
  | ⟨25,_⟩ => (3571499 / 12500000 : ℝ)
  | ⟨26,_⟩ => (143049517 / 500000000 : ℝ)
  | ⟨27,_⟩ => (286476749 / 1000000000 : ℝ)
  | ⟨28,_⟩ => (286853569 / 1000000000 : ℝ)
  | ⟨29,_⟩ => (287229493 / 1000000000 : ℝ)
  | ⟨30,_⟩ => (35950503 / 125000000 : ℝ)
  | ⟨31,_⟩ => (287978171 / 1000000000 : ℝ)
  | ⟨32,_⟩ => (288351437 / 1000000000 : ℝ)
  | ⟨33,_⟩ => (144361657 / 500000000 : ℝ)
  | ⟨34,_⟩ => (72273579 / 250000000 : ℝ)
  | ⟨35,_⟩ => (2261441 / 7812500 : ℝ)
  | ⟨36,_⟩ => (144916851 / 500000000 : ℝ)
  | ⟨37,_⟩ => (145101049 / 500000000 : ℝ)
  | ⟨38,_⟩ => (29056963 / 100000000 : ℝ)
  | ⟨39,_⟩ => (290935789 / 1000000000 : ℝ)
  | ⟨40,_⟩ => (29130109 / 100000000 : ℝ)
  | ⟨41,_⟩ => (14583277 / 50000000 : ℝ)
  | ⟨42,_⟩ => (292029139 / 1000000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12329Cell0 :
    0 ≤ cap12329 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12329 (parameters ⟨0,by decide⟩)
      (scalarRow12329.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12329 ⟨0,by decide⟩ ∧
    (scalarRow12329.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12329 ⟨0,by decide⟩ + (scalarRow12329.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12329.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12329.targetFrame := by
  norm_num [cap12329, scalarRow12329, sourceIndex, cell12329, BstLean.Part263.envelope, parameters]

theorem repair12329Cell1 :
    0 ≤ cap12329 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12329 (parameters ⟨1,by decide⟩)
      (scalarRow12329.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12329 ⟨1,by decide⟩ ∧
    (scalarRow12329.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12329 ⟨1,by decide⟩ + (scalarRow12329.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12329.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12329.targetFrame := by
  norm_num [cap12329, scalarRow12329, sourceIndex, cell12329, BstLean.Part263.envelope, parameters]

theorem repair12329Cell2 :
    0 ≤ cap12329 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12329 (parameters ⟨2,by decide⟩)
      (scalarRow12329.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12329 ⟨2,by decide⟩ ∧
    (scalarRow12329.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12329 ⟨2,by decide⟩ + (scalarRow12329.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12329.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12329.targetFrame := by
  norm_num [cap12329, scalarRow12329, sourceIndex, cell12329, BstLean.Part263.envelope, parameters]

theorem repair12329Cell3 :
    0 ≤ cap12329 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12329 (parameters ⟨3,by decide⟩)
      (scalarRow12329.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12329 ⟨3,by decide⟩ ∧
    (scalarRow12329.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12329 ⟨3,by decide⟩ + (scalarRow12329.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12329.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12329.targetFrame := by
  norm_num [cap12329, scalarRow12329, sourceIndex, cell12329, BstLean.Part263.envelope, parameters]

theorem repair12329Cell4 :
    0 ≤ cap12329 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12329 (parameters ⟨4,by decide⟩)
      (scalarRow12329.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12329 ⟨4,by decide⟩ ∧
    (scalarRow12329.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12329 ⟨4,by decide⟩ + (scalarRow12329.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12329.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12329.targetFrame := by
  norm_num [cap12329, scalarRow12329, sourceIndex, cell12329, BstLean.Part263.envelope, parameters]

theorem repair12329Cell5 :
    0 ≤ cap12329 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12329 (parameters ⟨5,by decide⟩)
      (scalarRow12329.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12329 ⟨5,by decide⟩ ∧
    (scalarRow12329.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12329 ⟨5,by decide⟩ + (scalarRow12329.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12329.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12329.targetFrame := by
  norm_num [cap12329, scalarRow12329, sourceIndex, cell12329, BstLean.Part263.envelope, parameters]

theorem repair12329Cell6 :
    0 ≤ cap12329 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12329 (parameters ⟨6,by decide⟩)
      (scalarRow12329.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12329 ⟨6,by decide⟩ ∧
    (scalarRow12329.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12329 ⟨6,by decide⟩ + (scalarRow12329.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12329.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12329.targetFrame := by
  norm_num [cap12329, scalarRow12329, sourceIndex, cell12329, BstLean.Part263.envelope, parameters]

theorem repair12329Cell7 :
    0 ≤ cap12329 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12329 (parameters ⟨7,by decide⟩)
      (scalarRow12329.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12329 ⟨7,by decide⟩ ∧
    (scalarRow12329.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12329 ⟨7,by decide⟩ + (scalarRow12329.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12329.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12329.targetFrame := by
  norm_num [cap12329, scalarRow12329, sourceIndex, cell12329, BstLean.Part263.envelope, parameters]

theorem repair12329Cell8 :
    0 ≤ cap12329 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12329 (parameters ⟨8,by decide⟩)
      (scalarRow12329.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12329 ⟨8,by decide⟩ ∧
    (scalarRow12329.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12329 ⟨8,by decide⟩ + (scalarRow12329.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12329.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12329.targetFrame := by
  norm_num [cap12329, scalarRow12329, sourceIndex, cell12329, BstLean.Part263.envelope, parameters]

theorem repair12329Cell9 :
    0 ≤ cap12329 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12329 (parameters ⟨9,by decide⟩)
      (scalarRow12329.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12329 ⟨9,by decide⟩ ∧
    (scalarRow12329.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12329 ⟨9,by decide⟩ + (scalarRow12329.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12329.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12329.targetFrame := by
  norm_num [cap12329, scalarRow12329, sourceIndex, cell12329, BstLean.Part263.envelope, parameters]

theorem repair12329Cell10 :
    0 ≤ cap12329 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12329 (parameters ⟨10,by decide⟩)
      (scalarRow12329.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12329 ⟨10,by decide⟩ ∧
    (scalarRow12329.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12329 ⟨10,by decide⟩ + (scalarRow12329.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12329.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12329.targetFrame := by
  norm_num [cap12329, scalarRow12329, sourceIndex, cell12329, BstLean.Part263.envelope, parameters]

theorem repair12329Cell11 :
    0 ≤ cap12329 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12329 (parameters ⟨11,by decide⟩)
      (scalarRow12329.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12329 ⟨11,by decide⟩ ∧
    (scalarRow12329.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12329 ⟨11,by decide⟩ + (scalarRow12329.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12329.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12329.targetFrame := by
  norm_num [cap12329, scalarRow12329, sourceIndex, cell12329, BstLean.Part263.envelope, parameters]

theorem repair12329Cell12 :
    0 ≤ cap12329 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12329 (parameters ⟨12,by decide⟩)
      (scalarRow12329.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12329 ⟨12,by decide⟩ ∧
    (scalarRow12329.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12329 ⟨12,by decide⟩ + (scalarRow12329.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12329.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12329.targetFrame := by
  norm_num [cap12329, scalarRow12329, sourceIndex, cell12329, BstLean.Part263.envelope, parameters]

theorem repair12329Cell13 :
    0 ≤ cap12329 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12329 (parameters ⟨13,by decide⟩)
      (scalarRow12329.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12329 ⟨13,by decide⟩ ∧
    (scalarRow12329.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12329 ⟨13,by decide⟩ + (scalarRow12329.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12329.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12329.targetFrame := by
  norm_num [cap12329, scalarRow12329, sourceIndex, cell12329, BstLean.Part263.envelope, parameters]

theorem repair12329Cell14 :
    0 ≤ cap12329 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12329 (parameters ⟨14,by decide⟩)
      (scalarRow12329.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12329 ⟨14,by decide⟩ ∧
    (scalarRow12329.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12329 ⟨14,by decide⟩ + (scalarRow12329.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12329.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12329.targetFrame := by
  norm_num [cap12329, scalarRow12329, sourceIndex, cell12329, BstLean.Part263.envelope, parameters]

theorem repair12329Cell15 :
    0 ≤ cap12329 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12329 (parameters ⟨15,by decide⟩)
      (scalarRow12329.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12329 ⟨15,by decide⟩ ∧
    (scalarRow12329.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12329 ⟨15,by decide⟩ + (scalarRow12329.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12329.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12329.targetFrame := by
  norm_num [cap12329, scalarRow12329, sourceIndex, cell12329, BstLean.Part263.envelope, parameters]

theorem repair12329Cell16 :
    0 ≤ cap12329 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12329 (parameters ⟨16,by decide⟩)
      (scalarRow12329.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12329 ⟨16,by decide⟩ ∧
    (scalarRow12329.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12329 ⟨16,by decide⟩ + (scalarRow12329.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12329.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12329.targetFrame := by
  norm_num [cap12329, scalarRow12329, sourceIndex, cell12329, BstLean.Part263.envelope, parameters]

theorem repair12329Cell17 :
    0 ≤ cap12329 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12329 (parameters ⟨17,by decide⟩)
      (scalarRow12329.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12329 ⟨17,by decide⟩ ∧
    (scalarRow12329.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12329 ⟨17,by decide⟩ + (scalarRow12329.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12329.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12329.targetFrame := by
  norm_num [cap12329, scalarRow12329, sourceIndex, cell12329, BstLean.Part263.envelope, parameters]

theorem repair12329Cell18 :
    0 ≤ cap12329 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12329 (parameters ⟨18,by decide⟩)
      (scalarRow12329.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12329 ⟨18,by decide⟩ ∧
    (scalarRow12329.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12329 ⟨18,by decide⟩ + (scalarRow12329.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12329.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12329.targetFrame := by
  norm_num [cap12329, scalarRow12329, sourceIndex, cell12329, BstLean.Part263.envelope, parameters]

theorem repair12329Cell19 :
    0 ≤ cap12329 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12329 (parameters ⟨19,by decide⟩)
      (scalarRow12329.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12329 ⟨19,by decide⟩ ∧
    (scalarRow12329.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12329 ⟨19,by decide⟩ + (scalarRow12329.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12329.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12329.targetFrame := by
  norm_num [cap12329, scalarRow12329, sourceIndex, cell12329, BstLean.Part263.envelope, parameters]

theorem repair12329Cell20 :
    0 ≤ cap12329 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12329 (parameters ⟨20,by decide⟩)
      (scalarRow12329.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12329 ⟨20,by decide⟩ ∧
    (scalarRow12329.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12329 ⟨20,by decide⟩ + (scalarRow12329.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12329.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12329.targetFrame := by
  norm_num [cap12329, scalarRow12329, sourceIndex, cell12329, BstLean.Part263.envelope, parameters]

theorem repair12329Cell21 :
    0 ≤ cap12329 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12329 (parameters ⟨21,by decide⟩)
      (scalarRow12329.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12329 ⟨21,by decide⟩ ∧
    (scalarRow12329.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12329 ⟨21,by decide⟩ + (scalarRow12329.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12329.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12329.targetFrame := by
  norm_num [cap12329, scalarRow12329, sourceIndex, cell12329, BstLean.Part263.envelope, parameters]

theorem repair12329Cell22 :
    0 ≤ cap12329 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12329 (parameters ⟨22,by decide⟩)
      (scalarRow12329.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12329 ⟨22,by decide⟩ ∧
    (scalarRow12329.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12329 ⟨22,by decide⟩ + (scalarRow12329.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12329.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12329.targetFrame := by
  norm_num [cap12329, scalarRow12329, sourceIndex, cell12329, BstLean.Part263.envelope, parameters]

theorem repair12329Cell23 :
    0 ≤ cap12329 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12329 (parameters ⟨23,by decide⟩)
      (scalarRow12329.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12329 ⟨23,by decide⟩ ∧
    (scalarRow12329.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12329 ⟨23,by decide⟩ + (scalarRow12329.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12329.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12329.targetFrame := by
  norm_num [cap12329, scalarRow12329, sourceIndex, cell12329, BstLean.Part263.envelope, parameters]

theorem repair12329Cell24 :
    0 ≤ cap12329 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12329 (parameters ⟨24,by decide⟩)
      (scalarRow12329.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12329 ⟨24,by decide⟩ ∧
    (scalarRow12329.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12329 ⟨24,by decide⟩ + (scalarRow12329.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12329.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12329.targetFrame := by
  norm_num [cap12329, scalarRow12329, sourceIndex, cell12329, BstLean.Part263.envelope, parameters]

theorem repair12329Cell25 :
    0 ≤ cap12329 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12329 (parameters ⟨25,by decide⟩)
      (scalarRow12329.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12329 ⟨25,by decide⟩ ∧
    (scalarRow12329.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12329 ⟨25,by decide⟩ + (scalarRow12329.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12329.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12329.targetFrame := by
  norm_num [cap12329, scalarRow12329, sourceIndex, cell12329, BstLean.Part263.envelope, parameters]

theorem repair12329Cell26 :
    0 ≤ cap12329 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12329 (parameters ⟨26,by decide⟩)
      (scalarRow12329.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12329 ⟨26,by decide⟩ ∧
    (scalarRow12329.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12329 ⟨26,by decide⟩ + (scalarRow12329.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12329.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12329.targetFrame := by
  norm_num [cap12329, scalarRow12329, sourceIndex, cell12329, BstLean.Part263.envelope, parameters]

theorem repair12329Cell27 :
    0 ≤ cap12329 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12329 (parameters ⟨27,by decide⟩)
      (scalarRow12329.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12329 ⟨27,by decide⟩ ∧
    (scalarRow12329.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12329 ⟨27,by decide⟩ + (scalarRow12329.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12329.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12329.targetFrame := by
  norm_num [cap12329, scalarRow12329, sourceIndex, cell12329, BstLean.Part263.envelope, parameters]

theorem repair12329Cell28 :
    0 ≤ cap12329 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12329 (parameters ⟨28,by decide⟩)
      (scalarRow12329.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12329 ⟨28,by decide⟩ ∧
    (scalarRow12329.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12329 ⟨28,by decide⟩ + (scalarRow12329.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12329.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12329.targetFrame := by
  norm_num [cap12329, scalarRow12329, sourceIndex, cell12329, BstLean.Part263.envelope, parameters]

theorem repair12329Cell29 :
    0 ≤ cap12329 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12329 (parameters ⟨29,by decide⟩)
      (scalarRow12329.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12329 ⟨29,by decide⟩ ∧
    (scalarRow12329.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12329 ⟨29,by decide⟩ + (scalarRow12329.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12329.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12329.targetFrame := by
  norm_num [cap12329, scalarRow12329, sourceIndex, cell12329, BstLean.Part263.envelope, parameters]

theorem repair12329Cell30 :
    0 ≤ cap12329 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12329 (parameters ⟨30,by decide⟩)
      (scalarRow12329.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12329 ⟨30,by decide⟩ ∧
    (scalarRow12329.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12329 ⟨30,by decide⟩ + (scalarRow12329.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12329.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12329.targetFrame := by
  norm_num [cap12329, scalarRow12329, sourceIndex, cell12329, BstLean.Part263.envelope, parameters]

theorem repair12329Cell31 :
    0 ≤ cap12329 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12329 (parameters ⟨31,by decide⟩)
      (scalarRow12329.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12329 ⟨31,by decide⟩ ∧
    (scalarRow12329.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12329 ⟨31,by decide⟩ + (scalarRow12329.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12329.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12329.targetFrame := by
  norm_num [cap12329, scalarRow12329, sourceIndex, cell12329, BstLean.Part263.envelope, parameters]

theorem repair12329Cell32 :
    0 ≤ cap12329 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12329 (parameters ⟨32,by decide⟩)
      (scalarRow12329.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12329 ⟨32,by decide⟩ ∧
    (scalarRow12329.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12329 ⟨32,by decide⟩ + (scalarRow12329.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12329.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12329.targetFrame := by
  norm_num [cap12329, scalarRow12329, sourceIndex, cell12329, BstLean.Part263.envelope, parameters]

theorem repair12329Cell33 :
    0 ≤ cap12329 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12329 (parameters ⟨33,by decide⟩)
      (scalarRow12329.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12329 ⟨33,by decide⟩ ∧
    (scalarRow12329.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12329 ⟨33,by decide⟩ + (scalarRow12329.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12329.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12329.targetFrame := by
  norm_num [cap12329, scalarRow12329, sourceIndex, cell12329, BstLean.Part263.envelope, parameters]

theorem repair12329Cell34 :
    0 ≤ cap12329 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12329 (parameters ⟨34,by decide⟩)
      (scalarRow12329.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12329 ⟨34,by decide⟩ ∧
    (scalarRow12329.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12329 ⟨34,by decide⟩ + (scalarRow12329.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12329.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12329.targetFrame := by
  norm_num [cap12329, scalarRow12329, sourceIndex, cell12329, BstLean.Part263.envelope, parameters]

theorem repair12329Cell35 :
    0 ≤ cap12329 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12329 (parameters ⟨35,by decide⟩)
      (scalarRow12329.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12329 ⟨35,by decide⟩ ∧
    (scalarRow12329.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12329 ⟨35,by decide⟩ + (scalarRow12329.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12329.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12329.targetFrame := by
  norm_num [cap12329, scalarRow12329, sourceIndex, cell12329, BstLean.Part263.envelope, parameters]

theorem repair12329Cell36 :
    0 ≤ cap12329 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12329 (parameters ⟨36,by decide⟩)
      (scalarRow12329.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12329 ⟨36,by decide⟩ ∧
    (scalarRow12329.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12329 ⟨36,by decide⟩ + (scalarRow12329.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12329.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12329.targetFrame := by
  norm_num [cap12329, scalarRow12329, sourceIndex, cell12329, BstLean.Part263.envelope, parameters]

theorem repair12329Cell37 :
    0 ≤ cap12329 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12329 (parameters ⟨37,by decide⟩)
      (scalarRow12329.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12329 ⟨37,by decide⟩ ∧
    (scalarRow12329.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12329 ⟨37,by decide⟩ + (scalarRow12329.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12329.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12329.targetFrame := by
  norm_num [cap12329, scalarRow12329, sourceIndex, cell12329, BstLean.Part263.envelope, parameters]

theorem repair12329Cell38 :
    0 ≤ cap12329 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12329 (parameters ⟨38,by decide⟩)
      (scalarRow12329.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12329 ⟨38,by decide⟩ ∧
    (scalarRow12329.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12329 ⟨38,by decide⟩ + (scalarRow12329.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12329.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12329.targetFrame := by
  norm_num [cap12329, scalarRow12329, sourceIndex, cell12329, BstLean.Part263.envelope, parameters]

theorem repair12329Cell39 :
    0 ≤ cap12329 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12329 (parameters ⟨39,by decide⟩)
      (scalarRow12329.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12329 ⟨39,by decide⟩ ∧
    (scalarRow12329.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12329 ⟨39,by decide⟩ + (scalarRow12329.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12329.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12329.targetFrame := by
  norm_num [cap12329, scalarRow12329, sourceIndex, cell12329, BstLean.Part263.envelope, parameters]

theorem repair12329Cell40 :
    0 ≤ cap12329 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12329 (parameters ⟨40,by decide⟩)
      (scalarRow12329.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12329 ⟨40,by decide⟩ ∧
    (scalarRow12329.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12329 ⟨40,by decide⟩ + (scalarRow12329.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12329.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12329.targetFrame := by
  norm_num [cap12329, scalarRow12329, sourceIndex, cell12329, BstLean.Part263.envelope, parameters]

theorem repair12329Cell41 :
    0 ≤ cap12329 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12329 (parameters ⟨41,by decide⟩)
      (scalarRow12329.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12329 ⟨41,by decide⟩ ∧
    (scalarRow12329.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12329 ⟨41,by decide⟩ + (scalarRow12329.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12329.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12329.targetFrame := by
  norm_num [cap12329, scalarRow12329, sourceIndex, cell12329, BstLean.Part263.envelope, parameters]

theorem repair12329Cell42 :
    0 ≤ cap12329 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12329 (parameters ⟨42,by decide⟩)
      (scalarRow12329.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12329 ⟨42,by decide⟩ ∧
    (scalarRow12329.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12329 ⟨42,by decide⟩ + (scalarRow12329.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12329.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12329.targetFrame := by
  norm_num [cap12329, scalarRow12329, sourceIndex, cell12329, BstLean.Part263.envelope, parameters]

theorem repair12329Cells (j : Fin 43) :
    0 ≤ cap12329 j ∧
    BstLean.Part263.envelope 12329 (parameters j) (scalarRow12329.table (sourceIndex j)).upper ≤ cap12329 j ∧
    (scalarRow12329.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12329 j + (scalarRow12329.table (sourceIndex j)).centre) /
      (scalarRow12329.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12329.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12329Cell0
  | ⟨1,_⟩ => exact repair12329Cell1
  | ⟨2,_⟩ => exact repair12329Cell2
  | ⟨3,_⟩ => exact repair12329Cell3
  | ⟨4,_⟩ => exact repair12329Cell4
  | ⟨5,_⟩ => exact repair12329Cell5
  | ⟨6,_⟩ => exact repair12329Cell6
  | ⟨7,_⟩ => exact repair12329Cell7
  | ⟨8,_⟩ => exact repair12329Cell8
  | ⟨9,_⟩ => exact repair12329Cell9
  | ⟨10,_⟩ => exact repair12329Cell10
  | ⟨11,_⟩ => exact repair12329Cell11
  | ⟨12,_⟩ => exact repair12329Cell12
  | ⟨13,_⟩ => exact repair12329Cell13
  | ⟨14,_⟩ => exact repair12329Cell14
  | ⟨15,_⟩ => exact repair12329Cell15
  | ⟨16,_⟩ => exact repair12329Cell16
  | ⟨17,_⟩ => exact repair12329Cell17
  | ⟨18,_⟩ => exact repair12329Cell18
  | ⟨19,_⟩ => exact repair12329Cell19
  | ⟨20,_⟩ => exact repair12329Cell20
  | ⟨21,_⟩ => exact repair12329Cell21
  | ⟨22,_⟩ => exact repair12329Cell22
  | ⟨23,_⟩ => exact repair12329Cell23
  | ⟨24,_⟩ => exact repair12329Cell24
  | ⟨25,_⟩ => exact repair12329Cell25
  | ⟨26,_⟩ => exact repair12329Cell26
  | ⟨27,_⟩ => exact repair12329Cell27
  | ⟨28,_⟩ => exact repair12329Cell28
  | ⟨29,_⟩ => exact repair12329Cell29
  | ⟨30,_⟩ => exact repair12329Cell30
  | ⟨31,_⟩ => exact repair12329Cell31
  | ⟨32,_⟩ => exact repair12329Cell32
  | ⟨33,_⟩ => exact repair12329Cell33
  | ⟨34,_⟩ => exact repair12329Cell34
  | ⟨35,_⟩ => exact repair12329Cell35
  | ⟨36,_⟩ => exact repair12329Cell36
  | ⟨37,_⟩ => exact repair12329Cell37
  | ⟨38,_⟩ => exact repair12329Cell38
  | ⟨39,_⟩ => exact repair12329Cell39
  | ⟨40,_⟩ => exact repair12329Cell40
  | ⟨41,_⟩ => exact repair12329Cell41
  | ⟨42,_⟩ => exact repair12329Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12329 : FrameRepair 12329 scalarRow12329 where
  cap := cap12329
  cap_nonneg := fun j => (repair12329Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12329])
  endpoint := fun j => (repair12329Cells j).2.1
  endpoint_upper := fun j => (repair12329Cells j).2.2.1
  frame := fun j => (repair12329Cells j).2.2.2

noncomputable def cap12330 : Fin 43 → ℝ
  | ⟨0,_⟩ => (137972401 / 500000000 : ℝ)
  | ⟨1,_⟩ => (276347393 / 1000000000 : ℝ)
  | ⟨2,_⟩ => (27674899 / 100000000 : ℝ)
  | ⟨3,_⟩ => (27714959 / 100000000 : ℝ)
  | ⟨4,_⟩ => (277549201 / 1000000000 : ℝ)
  | ⟨5,_⟩ => (138973911 / 500000000 : ℝ)
  | ⟨6,_⟩ => (278344983 / 1000000000 : ℝ)
  | ⟨7,_⟩ => (278741639 / 1000000000 : ℝ)
  | ⟨8,_⟩ => (279137319 / 1000000000 : ℝ)
  | ⟨9,_⟩ => (279532027 / 1000000000 : ℝ)
  | ⟨10,_⟩ => (55985153 / 200000000 : ℝ)
  | ⟨11,_⟩ => (56063611 / 200000000 : ℝ)
  | ⟨12,_⟩ => (70177467 / 250000000 : ℝ)
  | ⟨13,_⟩ => (56220047 / 200000000 : ℝ)
  | ⟨14,_⟩ => (56298107 / 200000000 : ℝ)
  | ⟨15,_⟩ => (56375947 / 200000000 : ℝ)
  | ⟨16,_⟩ => (141133997 / 500000000 : ℝ)
  | ⟨17,_⟩ => (282655321 / 1000000000 : ℝ)
  | ⟨18,_⟩ => (28304171 / 100000000 : ℝ)
  | ⟨19,_⟩ => (283427171 / 1000000000 : ℝ)
  | ⟨20,_⟩ => (141905853 / 500000000 : ℝ)
  | ⟨21,_⟩ => (71048831 / 250000000 : ℝ)
  | ⟨22,_⟩ => (284578019 / 1000000000 : ℝ)
  | ⟨23,_⟩ => (35619913 / 125000000 : ℝ)
  | ⟨24,_⟩ => (17833761 / 62500000 : ℝ)
  | ⟨25,_⟩ => (35714961 / 125000000 : ℝ)
  | ⟨26,_⟩ => (71524699 / 250000000 : ℝ)
  | ⟨27,_⟩ => (57295301 / 200000000 : ℝ)
  | ⟨28,_⟩ => (143426659 / 500000000 : ℝ)
  | ⟨29,_⟩ => (71807309 / 250000000 : ℝ)
  | ⟨30,_⟩ => (287603761 / 1000000000 : ℝ)
  | ⟨31,_⟩ => (143988951 / 500000000 : ℝ)
  | ⟨32,_⟩ => (288351163 / 1000000000 : ℝ)
  | ⟨33,_⟩ => (144361517 / 500000000 : ℝ)
  | ⟨34,_⟩ => (28909403 / 100000000 : ℝ)
  | ⟨35,_⟩ => (57892831 / 200000000 : ℝ)
  | ⟨36,_⟩ => (72458351 / 250000000 : ℝ)
  | ⟨37,_⟩ => (145100897 / 500000000 : ℝ)
  | ⟨38,_⟩ => (290569319 / 1000000000 : ℝ)
  | ⟨39,_⟩ => (290935473 / 1000000000 : ℝ)
  | ⟨40,_⟩ => (9103149 / 31250000 : ℝ)
  | ⟨41,_⟩ => (72916303 / 250000000 : ℝ)
  | ⟨42,_⟩ => (73007201 / 250000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12330Cell0 :
    0 ≤ cap12330 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12330 (parameters ⟨0,by decide⟩)
      (scalarRow12330.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12330 ⟨0,by decide⟩ ∧
    (scalarRow12330.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12330 ⟨0,by decide⟩ + (scalarRow12330.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12330.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12330.targetFrame := by
  norm_num [cap12330, scalarRow12330, sourceIndex, cell12330, BstLean.Part263.envelope, parameters]

theorem repair12330Cell1 :
    0 ≤ cap12330 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12330 (parameters ⟨1,by decide⟩)
      (scalarRow12330.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12330 ⟨1,by decide⟩ ∧
    (scalarRow12330.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12330 ⟨1,by decide⟩ + (scalarRow12330.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12330.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12330.targetFrame := by
  norm_num [cap12330, scalarRow12330, sourceIndex, cell12330, BstLean.Part263.envelope, parameters]

theorem repair12330Cell2 :
    0 ≤ cap12330 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12330 (parameters ⟨2,by decide⟩)
      (scalarRow12330.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12330 ⟨2,by decide⟩ ∧
    (scalarRow12330.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12330 ⟨2,by decide⟩ + (scalarRow12330.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12330.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12330.targetFrame := by
  norm_num [cap12330, scalarRow12330, sourceIndex, cell12330, BstLean.Part263.envelope, parameters]

theorem repair12330Cell3 :
    0 ≤ cap12330 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12330 (parameters ⟨3,by decide⟩)
      (scalarRow12330.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12330 ⟨3,by decide⟩ ∧
    (scalarRow12330.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12330 ⟨3,by decide⟩ + (scalarRow12330.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12330.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12330.targetFrame := by
  norm_num [cap12330, scalarRow12330, sourceIndex, cell12330, BstLean.Part263.envelope, parameters]

theorem repair12330Cell4 :
    0 ≤ cap12330 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12330 (parameters ⟨4,by decide⟩)
      (scalarRow12330.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12330 ⟨4,by decide⟩ ∧
    (scalarRow12330.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12330 ⟨4,by decide⟩ + (scalarRow12330.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12330.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12330.targetFrame := by
  norm_num [cap12330, scalarRow12330, sourceIndex, cell12330, BstLean.Part263.envelope, parameters]

theorem repair12330Cell5 :
    0 ≤ cap12330 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12330 (parameters ⟨5,by decide⟩)
      (scalarRow12330.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12330 ⟨5,by decide⟩ ∧
    (scalarRow12330.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12330 ⟨5,by decide⟩ + (scalarRow12330.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12330.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12330.targetFrame := by
  norm_num [cap12330, scalarRow12330, sourceIndex, cell12330, BstLean.Part263.envelope, parameters]

theorem repair12330Cell6 :
    0 ≤ cap12330 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12330 (parameters ⟨6,by decide⟩)
      (scalarRow12330.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12330 ⟨6,by decide⟩ ∧
    (scalarRow12330.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12330 ⟨6,by decide⟩ + (scalarRow12330.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12330.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12330.targetFrame := by
  norm_num [cap12330, scalarRow12330, sourceIndex, cell12330, BstLean.Part263.envelope, parameters]

theorem repair12330Cell7 :
    0 ≤ cap12330 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12330 (parameters ⟨7,by decide⟩)
      (scalarRow12330.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12330 ⟨7,by decide⟩ ∧
    (scalarRow12330.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12330 ⟨7,by decide⟩ + (scalarRow12330.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12330.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12330.targetFrame := by
  norm_num [cap12330, scalarRow12330, sourceIndex, cell12330, BstLean.Part263.envelope, parameters]

theorem repair12330Cell8 :
    0 ≤ cap12330 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12330 (parameters ⟨8,by decide⟩)
      (scalarRow12330.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12330 ⟨8,by decide⟩ ∧
    (scalarRow12330.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12330 ⟨8,by decide⟩ + (scalarRow12330.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12330.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12330.targetFrame := by
  norm_num [cap12330, scalarRow12330, sourceIndex, cell12330, BstLean.Part263.envelope, parameters]

theorem repair12330Cell9 :
    0 ≤ cap12330 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12330 (parameters ⟨9,by decide⟩)
      (scalarRow12330.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12330 ⟨9,by decide⟩ ∧
    (scalarRow12330.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12330 ⟨9,by decide⟩ + (scalarRow12330.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12330.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12330.targetFrame := by
  norm_num [cap12330, scalarRow12330, sourceIndex, cell12330, BstLean.Part263.envelope, parameters]

theorem repair12330Cell10 :
    0 ≤ cap12330 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12330 (parameters ⟨10,by decide⟩)
      (scalarRow12330.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12330 ⟨10,by decide⟩ ∧
    (scalarRow12330.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12330 ⟨10,by decide⟩ + (scalarRow12330.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12330.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12330.targetFrame := by
  norm_num [cap12330, scalarRow12330, sourceIndex, cell12330, BstLean.Part263.envelope, parameters]

theorem repair12330Cell11 :
    0 ≤ cap12330 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12330 (parameters ⟨11,by decide⟩)
      (scalarRow12330.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12330 ⟨11,by decide⟩ ∧
    (scalarRow12330.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12330 ⟨11,by decide⟩ + (scalarRow12330.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12330.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12330.targetFrame := by
  norm_num [cap12330, scalarRow12330, sourceIndex, cell12330, BstLean.Part263.envelope, parameters]

theorem repair12330Cell12 :
    0 ≤ cap12330 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12330 (parameters ⟨12,by decide⟩)
      (scalarRow12330.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12330 ⟨12,by decide⟩ ∧
    (scalarRow12330.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12330 ⟨12,by decide⟩ + (scalarRow12330.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12330.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12330.targetFrame := by
  norm_num [cap12330, scalarRow12330, sourceIndex, cell12330, BstLean.Part263.envelope, parameters]

theorem repair12330Cell13 :
    0 ≤ cap12330 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12330 (parameters ⟨13,by decide⟩)
      (scalarRow12330.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12330 ⟨13,by decide⟩ ∧
    (scalarRow12330.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12330 ⟨13,by decide⟩ + (scalarRow12330.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12330.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12330.targetFrame := by
  norm_num [cap12330, scalarRow12330, sourceIndex, cell12330, BstLean.Part263.envelope, parameters]

theorem repair12330Cell14 :
    0 ≤ cap12330 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12330 (parameters ⟨14,by decide⟩)
      (scalarRow12330.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12330 ⟨14,by decide⟩ ∧
    (scalarRow12330.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12330 ⟨14,by decide⟩ + (scalarRow12330.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12330.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12330.targetFrame := by
  norm_num [cap12330, scalarRow12330, sourceIndex, cell12330, BstLean.Part263.envelope, parameters]

theorem repair12330Cell15 :
    0 ≤ cap12330 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12330 (parameters ⟨15,by decide⟩)
      (scalarRow12330.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12330 ⟨15,by decide⟩ ∧
    (scalarRow12330.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12330 ⟨15,by decide⟩ + (scalarRow12330.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12330.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12330.targetFrame := by
  norm_num [cap12330, scalarRow12330, sourceIndex, cell12330, BstLean.Part263.envelope, parameters]

theorem repair12330Cell16 :
    0 ≤ cap12330 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12330 (parameters ⟨16,by decide⟩)
      (scalarRow12330.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12330 ⟨16,by decide⟩ ∧
    (scalarRow12330.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12330 ⟨16,by decide⟩ + (scalarRow12330.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12330.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12330.targetFrame := by
  norm_num [cap12330, scalarRow12330, sourceIndex, cell12330, BstLean.Part263.envelope, parameters]

theorem repair12330Cell17 :
    0 ≤ cap12330 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12330 (parameters ⟨17,by decide⟩)
      (scalarRow12330.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12330 ⟨17,by decide⟩ ∧
    (scalarRow12330.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12330 ⟨17,by decide⟩ + (scalarRow12330.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12330.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12330.targetFrame := by
  norm_num [cap12330, scalarRow12330, sourceIndex, cell12330, BstLean.Part263.envelope, parameters]

theorem repair12330Cell18 :
    0 ≤ cap12330 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12330 (parameters ⟨18,by decide⟩)
      (scalarRow12330.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12330 ⟨18,by decide⟩ ∧
    (scalarRow12330.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12330 ⟨18,by decide⟩ + (scalarRow12330.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12330.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12330.targetFrame := by
  norm_num [cap12330, scalarRow12330, sourceIndex, cell12330, BstLean.Part263.envelope, parameters]

theorem repair12330Cell19 :
    0 ≤ cap12330 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12330 (parameters ⟨19,by decide⟩)
      (scalarRow12330.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12330 ⟨19,by decide⟩ ∧
    (scalarRow12330.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12330 ⟨19,by decide⟩ + (scalarRow12330.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12330.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12330.targetFrame := by
  norm_num [cap12330, scalarRow12330, sourceIndex, cell12330, BstLean.Part263.envelope, parameters]

theorem repair12330Cell20 :
    0 ≤ cap12330 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12330 (parameters ⟨20,by decide⟩)
      (scalarRow12330.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12330 ⟨20,by decide⟩ ∧
    (scalarRow12330.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12330 ⟨20,by decide⟩ + (scalarRow12330.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12330.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12330.targetFrame := by
  norm_num [cap12330, scalarRow12330, sourceIndex, cell12330, BstLean.Part263.envelope, parameters]

theorem repair12330Cell21 :
    0 ≤ cap12330 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12330 (parameters ⟨21,by decide⟩)
      (scalarRow12330.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12330 ⟨21,by decide⟩ ∧
    (scalarRow12330.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12330 ⟨21,by decide⟩ + (scalarRow12330.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12330.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12330.targetFrame := by
  norm_num [cap12330, scalarRow12330, sourceIndex, cell12330, BstLean.Part263.envelope, parameters]

theorem repair12330Cell22 :
    0 ≤ cap12330 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12330 (parameters ⟨22,by decide⟩)
      (scalarRow12330.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12330 ⟨22,by decide⟩ ∧
    (scalarRow12330.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12330 ⟨22,by decide⟩ + (scalarRow12330.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12330.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12330.targetFrame := by
  norm_num [cap12330, scalarRow12330, sourceIndex, cell12330, BstLean.Part263.envelope, parameters]

theorem repair12330Cell23 :
    0 ≤ cap12330 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12330 (parameters ⟨23,by decide⟩)
      (scalarRow12330.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12330 ⟨23,by decide⟩ ∧
    (scalarRow12330.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12330 ⟨23,by decide⟩ + (scalarRow12330.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12330.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12330.targetFrame := by
  norm_num [cap12330, scalarRow12330, sourceIndex, cell12330, BstLean.Part263.envelope, parameters]

theorem repair12330Cell24 :
    0 ≤ cap12330 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12330 (parameters ⟨24,by decide⟩)
      (scalarRow12330.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12330 ⟨24,by decide⟩ ∧
    (scalarRow12330.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12330 ⟨24,by decide⟩ + (scalarRow12330.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12330.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12330.targetFrame := by
  norm_num [cap12330, scalarRow12330, sourceIndex, cell12330, BstLean.Part263.envelope, parameters]

theorem repair12330Cell25 :
    0 ≤ cap12330 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12330 (parameters ⟨25,by decide⟩)
      (scalarRow12330.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12330 ⟨25,by decide⟩ ∧
    (scalarRow12330.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12330 ⟨25,by decide⟩ + (scalarRow12330.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12330.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12330.targetFrame := by
  norm_num [cap12330, scalarRow12330, sourceIndex, cell12330, BstLean.Part263.envelope, parameters]

theorem repair12330Cell26 :
    0 ≤ cap12330 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12330 (parameters ⟨26,by decide⟩)
      (scalarRow12330.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12330 ⟨26,by decide⟩ ∧
    (scalarRow12330.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12330 ⟨26,by decide⟩ + (scalarRow12330.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12330.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12330.targetFrame := by
  norm_num [cap12330, scalarRow12330, sourceIndex, cell12330, BstLean.Part263.envelope, parameters]

theorem repair12330Cell27 :
    0 ≤ cap12330 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12330 (parameters ⟨27,by decide⟩)
      (scalarRow12330.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12330 ⟨27,by decide⟩ ∧
    (scalarRow12330.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12330 ⟨27,by decide⟩ + (scalarRow12330.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12330.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12330.targetFrame := by
  norm_num [cap12330, scalarRow12330, sourceIndex, cell12330, BstLean.Part263.envelope, parameters]

theorem repair12330Cell28 :
    0 ≤ cap12330 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12330 (parameters ⟨28,by decide⟩)
      (scalarRow12330.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12330 ⟨28,by decide⟩ ∧
    (scalarRow12330.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12330 ⟨28,by decide⟩ + (scalarRow12330.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12330.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12330.targetFrame := by
  norm_num [cap12330, scalarRow12330, sourceIndex, cell12330, BstLean.Part263.envelope, parameters]

theorem repair12330Cell29 :
    0 ≤ cap12330 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12330 (parameters ⟨29,by decide⟩)
      (scalarRow12330.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12330 ⟨29,by decide⟩ ∧
    (scalarRow12330.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12330 ⟨29,by decide⟩ + (scalarRow12330.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12330.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12330.targetFrame := by
  norm_num [cap12330, scalarRow12330, sourceIndex, cell12330, BstLean.Part263.envelope, parameters]

theorem repair12330Cell30 :
    0 ≤ cap12330 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12330 (parameters ⟨30,by decide⟩)
      (scalarRow12330.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12330 ⟨30,by decide⟩ ∧
    (scalarRow12330.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12330 ⟨30,by decide⟩ + (scalarRow12330.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12330.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12330.targetFrame := by
  norm_num [cap12330, scalarRow12330, sourceIndex, cell12330, BstLean.Part263.envelope, parameters]

theorem repair12330Cell31 :
    0 ≤ cap12330 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12330 (parameters ⟨31,by decide⟩)
      (scalarRow12330.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12330 ⟨31,by decide⟩ ∧
    (scalarRow12330.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12330 ⟨31,by decide⟩ + (scalarRow12330.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12330.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12330.targetFrame := by
  norm_num [cap12330, scalarRow12330, sourceIndex, cell12330, BstLean.Part263.envelope, parameters]

theorem repair12330Cell32 :
    0 ≤ cap12330 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12330 (parameters ⟨32,by decide⟩)
      (scalarRow12330.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12330 ⟨32,by decide⟩ ∧
    (scalarRow12330.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12330 ⟨32,by decide⟩ + (scalarRow12330.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12330.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12330.targetFrame := by
  norm_num [cap12330, scalarRow12330, sourceIndex, cell12330, BstLean.Part263.envelope, parameters]

theorem repair12330Cell33 :
    0 ≤ cap12330 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12330 (parameters ⟨33,by decide⟩)
      (scalarRow12330.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12330 ⟨33,by decide⟩ ∧
    (scalarRow12330.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12330 ⟨33,by decide⟩ + (scalarRow12330.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12330.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12330.targetFrame := by
  norm_num [cap12330, scalarRow12330, sourceIndex, cell12330, BstLean.Part263.envelope, parameters]

theorem repair12330Cell34 :
    0 ≤ cap12330 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12330 (parameters ⟨34,by decide⟩)
      (scalarRow12330.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12330 ⟨34,by decide⟩ ∧
    (scalarRow12330.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12330 ⟨34,by decide⟩ + (scalarRow12330.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12330.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12330.targetFrame := by
  norm_num [cap12330, scalarRow12330, sourceIndex, cell12330, BstLean.Part263.envelope, parameters]

theorem repair12330Cell35 :
    0 ≤ cap12330 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12330 (parameters ⟨35,by decide⟩)
      (scalarRow12330.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12330 ⟨35,by decide⟩ ∧
    (scalarRow12330.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12330 ⟨35,by decide⟩ + (scalarRow12330.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12330.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12330.targetFrame := by
  norm_num [cap12330, scalarRow12330, sourceIndex, cell12330, BstLean.Part263.envelope, parameters]

theorem repair12330Cell36 :
    0 ≤ cap12330 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12330 (parameters ⟨36,by decide⟩)
      (scalarRow12330.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12330 ⟨36,by decide⟩ ∧
    (scalarRow12330.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12330 ⟨36,by decide⟩ + (scalarRow12330.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12330.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12330.targetFrame := by
  norm_num [cap12330, scalarRow12330, sourceIndex, cell12330, BstLean.Part263.envelope, parameters]

theorem repair12330Cell37 :
    0 ≤ cap12330 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12330 (parameters ⟨37,by decide⟩)
      (scalarRow12330.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12330 ⟨37,by decide⟩ ∧
    (scalarRow12330.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12330 ⟨37,by decide⟩ + (scalarRow12330.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12330.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12330.targetFrame := by
  norm_num [cap12330, scalarRow12330, sourceIndex, cell12330, BstLean.Part263.envelope, parameters]

theorem repair12330Cell38 :
    0 ≤ cap12330 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12330 (parameters ⟨38,by decide⟩)
      (scalarRow12330.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12330 ⟨38,by decide⟩ ∧
    (scalarRow12330.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12330 ⟨38,by decide⟩ + (scalarRow12330.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12330.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12330.targetFrame := by
  norm_num [cap12330, scalarRow12330, sourceIndex, cell12330, BstLean.Part263.envelope, parameters]

theorem repair12330Cell39 :
    0 ≤ cap12330 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12330 (parameters ⟨39,by decide⟩)
      (scalarRow12330.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12330 ⟨39,by decide⟩ ∧
    (scalarRow12330.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12330 ⟨39,by decide⟩ + (scalarRow12330.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12330.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12330.targetFrame := by
  norm_num [cap12330, scalarRow12330, sourceIndex, cell12330, BstLean.Part263.envelope, parameters]

theorem repair12330Cell40 :
    0 ≤ cap12330 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12330 (parameters ⟨40,by decide⟩)
      (scalarRow12330.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12330 ⟨40,by decide⟩ ∧
    (scalarRow12330.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12330 ⟨40,by decide⟩ + (scalarRow12330.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12330.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12330.targetFrame := by
  norm_num [cap12330, scalarRow12330, sourceIndex, cell12330, BstLean.Part263.envelope, parameters]

theorem repair12330Cell41 :
    0 ≤ cap12330 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12330 (parameters ⟨41,by decide⟩)
      (scalarRow12330.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12330 ⟨41,by decide⟩ ∧
    (scalarRow12330.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12330 ⟨41,by decide⟩ + (scalarRow12330.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12330.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12330.targetFrame := by
  norm_num [cap12330, scalarRow12330, sourceIndex, cell12330, BstLean.Part263.envelope, parameters]

theorem repair12330Cell42 :
    0 ≤ cap12330 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12330 (parameters ⟨42,by decide⟩)
      (scalarRow12330.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12330 ⟨42,by decide⟩ ∧
    (scalarRow12330.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12330 ⟨42,by decide⟩ + (scalarRow12330.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12330.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12330.targetFrame := by
  norm_num [cap12330, scalarRow12330, sourceIndex, cell12330, BstLean.Part263.envelope, parameters]

theorem repair12330Cells (j : Fin 43) :
    0 ≤ cap12330 j ∧
    BstLean.Part263.envelope 12330 (parameters j) (scalarRow12330.table (sourceIndex j)).upper ≤ cap12330 j ∧
    (scalarRow12330.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12330 j + (scalarRow12330.table (sourceIndex j)).centre) /
      (scalarRow12330.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12330.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12330Cell0
  | ⟨1,_⟩ => exact repair12330Cell1
  | ⟨2,_⟩ => exact repair12330Cell2
  | ⟨3,_⟩ => exact repair12330Cell3
  | ⟨4,_⟩ => exact repair12330Cell4
  | ⟨5,_⟩ => exact repair12330Cell5
  | ⟨6,_⟩ => exact repair12330Cell6
  | ⟨7,_⟩ => exact repair12330Cell7
  | ⟨8,_⟩ => exact repair12330Cell8
  | ⟨9,_⟩ => exact repair12330Cell9
  | ⟨10,_⟩ => exact repair12330Cell10
  | ⟨11,_⟩ => exact repair12330Cell11
  | ⟨12,_⟩ => exact repair12330Cell12
  | ⟨13,_⟩ => exact repair12330Cell13
  | ⟨14,_⟩ => exact repair12330Cell14
  | ⟨15,_⟩ => exact repair12330Cell15
  | ⟨16,_⟩ => exact repair12330Cell16
  | ⟨17,_⟩ => exact repair12330Cell17
  | ⟨18,_⟩ => exact repair12330Cell18
  | ⟨19,_⟩ => exact repair12330Cell19
  | ⟨20,_⟩ => exact repair12330Cell20
  | ⟨21,_⟩ => exact repair12330Cell21
  | ⟨22,_⟩ => exact repair12330Cell22
  | ⟨23,_⟩ => exact repair12330Cell23
  | ⟨24,_⟩ => exact repair12330Cell24
  | ⟨25,_⟩ => exact repair12330Cell25
  | ⟨26,_⟩ => exact repair12330Cell26
  | ⟨27,_⟩ => exact repair12330Cell27
  | ⟨28,_⟩ => exact repair12330Cell28
  | ⟨29,_⟩ => exact repair12330Cell29
  | ⟨30,_⟩ => exact repair12330Cell30
  | ⟨31,_⟩ => exact repair12330Cell31
  | ⟨32,_⟩ => exact repair12330Cell32
  | ⟨33,_⟩ => exact repair12330Cell33
  | ⟨34,_⟩ => exact repair12330Cell34
  | ⟨35,_⟩ => exact repair12330Cell35
  | ⟨36,_⟩ => exact repair12330Cell36
  | ⟨37,_⟩ => exact repair12330Cell37
  | ⟨38,_⟩ => exact repair12330Cell38
  | ⟨39,_⟩ => exact repair12330Cell39
  | ⟨40,_⟩ => exact repair12330Cell40
  | ⟨41,_⟩ => exact repair12330Cell41
  | ⟨42,_⟩ => exact repair12330Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12330 : FrameRepair 12330 scalarRow12330 where
  cap := cap12330
  cap_nonneg := fun j => (repair12330Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12330])
  endpoint := fun j => (repair12330Cells j).2.1
  endpoint_upper := fun j => (repair12330Cells j).2.2.1
  frame := fun j => (repair12330Cells j).2.2.2

noncomputable def cap12331 : Fin 43 → ℝ
  | ⟨0,_⟩ => (275944727 / 1000000000 : ℝ)
  | ⟨1,_⟩ => (276347311 / 1000000000 : ℝ)
  | ⟨2,_⟩ => (138374451 / 500000000 : ℝ)
  | ⟨3,_⟩ => (34643687 / 125000000 : ℝ)
  | ⟨4,_⟩ => (2775491 / 10000000 : ℝ)
  | ⟨5,_⟩ => (55589543 / 200000000 : ℝ)
  | ⟨6,_⟩ => (27834487 / 100000000 : ℝ)
  | ⟨7,_⟩ => (278741519 / 1000000000 : ℝ)
  | ⟨8,_⟩ => (279137193 / 1000000000 : ℝ)
  | ⟨9,_⟩ => (55906379 / 200000000 : ℝ)
  | ⟨10,_⟩ => (139962813 / 500000000 : ℝ)
  | ⟨11,_⟩ => (28031791 / 100000000 : ℝ)
  | ⟨12,_⟩ => (280709717 / 1000000000 : ℝ)
  | ⟨13,_⟩ => (281100077 / 1000000000 : ℝ)
  | ⟨14,_⟩ => (281490371 / 1000000000 : ℝ)
  | ⟨15,_⟩ => (56375913 / 200000000 : ℝ)
  | ⟨16,_⟩ => (282267817 / 1000000000 : ℝ)
  | ⟨17,_⟩ => (282655139 / 1000000000 : ℝ)
  | ⟨18,_⟩ => (283041521 / 1000000000 : ℝ)
  | ⟨19,_⟩ => (8857093 / 31250000 : ℝ)
  | ⟨20,_⟩ => (17738219 / 62500000 : ℝ)
  | ⟨21,_⟩ => (71048779 / 250000000 : ℝ)
  | ⟨22,_⟩ => (56915561 / 200000000 : ℝ)
  | ⟨23,_⟩ => (71239771 / 250000000 : ℝ)
  | ⟨24,_⟩ => (5706799 / 20000000 : ℝ)
  | ⟨25,_⟩ => (8928733 / 31250000 : ℝ)
  | ⟨26,_⟩ => (143049279 / 500000000 : ℝ)
  | ⟨27,_⟩ => (286476261 / 1000000000 : ℝ)
  | ⟨28,_⟩ => (71713267 / 250000000 : ℝ)
  | ⟨29,_⟩ => (14361449 / 50000000 : ℝ)
  | ⟨30,_⟩ => (287603499 / 1000000000 : ℝ)
  | ⟨31,_⟩ => (143988817 / 500000000 : ℝ)
  | ⟨32,_⟩ => (36043861 / 125000000 : ℝ)
  | ⟨33,_⟩ => (288722753 / 1000000000 : ℝ)
  | ⟨34,_⟩ => (289093743 / 1000000000 : ℝ)
  | ⟨35,_⟩ => (144731931 / 500000000 : ℝ)
  | ⟨36,_⟩ => (57966621 / 200000000 : ℝ)
  | ⟨37,_⟩ => (290201489 / 1000000000 : ℝ)
  | ⟨38,_⟩ => (290569009 / 1000000000 : ℝ)
  | ⟨39,_⟩ => (72733789 / 250000000 : ℝ)
  | ⟨40,_⟩ => (58260089 / 200000000 : ℝ)
  | ⟨41,_⟩ => (291664883 / 1000000000 : ℝ)
  | ⟨42,_⟩ => (29202847 / 100000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12331Cell0 :
    0 ≤ cap12331 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12331 (parameters ⟨0,by decide⟩)
      (scalarRow12331.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12331 ⟨0,by decide⟩ ∧
    (scalarRow12331.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12331 ⟨0,by decide⟩ + (scalarRow12331.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12331.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12331.targetFrame := by
  norm_num [cap12331, scalarRow12331, sourceIndex, cell12331, BstLean.Part263.envelope, parameters]

theorem repair12331Cell1 :
    0 ≤ cap12331 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12331 (parameters ⟨1,by decide⟩)
      (scalarRow12331.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12331 ⟨1,by decide⟩ ∧
    (scalarRow12331.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12331 ⟨1,by decide⟩ + (scalarRow12331.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12331.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12331.targetFrame := by
  norm_num [cap12331, scalarRow12331, sourceIndex, cell12331, BstLean.Part263.envelope, parameters]

theorem repair12331Cell2 :
    0 ≤ cap12331 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12331 (parameters ⟨2,by decide⟩)
      (scalarRow12331.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12331 ⟨2,by decide⟩ ∧
    (scalarRow12331.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12331 ⟨2,by decide⟩ + (scalarRow12331.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12331.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12331.targetFrame := by
  norm_num [cap12331, scalarRow12331, sourceIndex, cell12331, BstLean.Part263.envelope, parameters]

theorem repair12331Cell3 :
    0 ≤ cap12331 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12331 (parameters ⟨3,by decide⟩)
      (scalarRow12331.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12331 ⟨3,by decide⟩ ∧
    (scalarRow12331.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12331 ⟨3,by decide⟩ + (scalarRow12331.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12331.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12331.targetFrame := by
  norm_num [cap12331, scalarRow12331, sourceIndex, cell12331, BstLean.Part263.envelope, parameters]

theorem repair12331Cell4 :
    0 ≤ cap12331 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12331 (parameters ⟨4,by decide⟩)
      (scalarRow12331.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12331 ⟨4,by decide⟩ ∧
    (scalarRow12331.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12331 ⟨4,by decide⟩ + (scalarRow12331.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12331.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12331.targetFrame := by
  norm_num [cap12331, scalarRow12331, sourceIndex, cell12331, BstLean.Part263.envelope, parameters]

theorem repair12331Cell5 :
    0 ≤ cap12331 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12331 (parameters ⟨5,by decide⟩)
      (scalarRow12331.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12331 ⟨5,by decide⟩ ∧
    (scalarRow12331.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12331 ⟨5,by decide⟩ + (scalarRow12331.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12331.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12331.targetFrame := by
  norm_num [cap12331, scalarRow12331, sourceIndex, cell12331, BstLean.Part263.envelope, parameters]

theorem repair12331Cell6 :
    0 ≤ cap12331 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12331 (parameters ⟨6,by decide⟩)
      (scalarRow12331.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12331 ⟨6,by decide⟩ ∧
    (scalarRow12331.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12331 ⟨6,by decide⟩ + (scalarRow12331.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12331.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12331.targetFrame := by
  norm_num [cap12331, scalarRow12331, sourceIndex, cell12331, BstLean.Part263.envelope, parameters]

theorem repair12331Cell7 :
    0 ≤ cap12331 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12331 (parameters ⟨7,by decide⟩)
      (scalarRow12331.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12331 ⟨7,by decide⟩ ∧
    (scalarRow12331.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12331 ⟨7,by decide⟩ + (scalarRow12331.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12331.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12331.targetFrame := by
  norm_num [cap12331, scalarRow12331, sourceIndex, cell12331, BstLean.Part263.envelope, parameters]

theorem repair12331Cell8 :
    0 ≤ cap12331 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12331 (parameters ⟨8,by decide⟩)
      (scalarRow12331.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12331 ⟨8,by decide⟩ ∧
    (scalarRow12331.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12331 ⟨8,by decide⟩ + (scalarRow12331.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12331.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12331.targetFrame := by
  norm_num [cap12331, scalarRow12331, sourceIndex, cell12331, BstLean.Part263.envelope, parameters]

theorem repair12331Cell9 :
    0 ≤ cap12331 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12331 (parameters ⟨9,by decide⟩)
      (scalarRow12331.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12331 ⟨9,by decide⟩ ∧
    (scalarRow12331.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12331 ⟨9,by decide⟩ + (scalarRow12331.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12331.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12331.targetFrame := by
  norm_num [cap12331, scalarRow12331, sourceIndex, cell12331, BstLean.Part263.envelope, parameters]

theorem repair12331Cell10 :
    0 ≤ cap12331 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12331 (parameters ⟨10,by decide⟩)
      (scalarRow12331.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12331 ⟨10,by decide⟩ ∧
    (scalarRow12331.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12331 ⟨10,by decide⟩ + (scalarRow12331.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12331.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12331.targetFrame := by
  norm_num [cap12331, scalarRow12331, sourceIndex, cell12331, BstLean.Part263.envelope, parameters]

theorem repair12331Cell11 :
    0 ≤ cap12331 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12331 (parameters ⟨11,by decide⟩)
      (scalarRow12331.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12331 ⟨11,by decide⟩ ∧
    (scalarRow12331.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12331 ⟨11,by decide⟩ + (scalarRow12331.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12331.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12331.targetFrame := by
  norm_num [cap12331, scalarRow12331, sourceIndex, cell12331, BstLean.Part263.envelope, parameters]

theorem repair12331Cell12 :
    0 ≤ cap12331 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12331 (parameters ⟨12,by decide⟩)
      (scalarRow12331.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12331 ⟨12,by decide⟩ ∧
    (scalarRow12331.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12331 ⟨12,by decide⟩ + (scalarRow12331.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12331.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12331.targetFrame := by
  norm_num [cap12331, scalarRow12331, sourceIndex, cell12331, BstLean.Part263.envelope, parameters]

theorem repair12331Cell13 :
    0 ≤ cap12331 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12331 (parameters ⟨13,by decide⟩)
      (scalarRow12331.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12331 ⟨13,by decide⟩ ∧
    (scalarRow12331.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12331 ⟨13,by decide⟩ + (scalarRow12331.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12331.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12331.targetFrame := by
  norm_num [cap12331, scalarRow12331, sourceIndex, cell12331, BstLean.Part263.envelope, parameters]

theorem repair12331Cell14 :
    0 ≤ cap12331 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12331 (parameters ⟨14,by decide⟩)
      (scalarRow12331.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12331 ⟨14,by decide⟩ ∧
    (scalarRow12331.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12331 ⟨14,by decide⟩ + (scalarRow12331.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12331.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12331.targetFrame := by
  norm_num [cap12331, scalarRow12331, sourceIndex, cell12331, BstLean.Part263.envelope, parameters]

theorem repair12331Cell15 :
    0 ≤ cap12331 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12331 (parameters ⟨15,by decide⟩)
      (scalarRow12331.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12331 ⟨15,by decide⟩ ∧
    (scalarRow12331.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12331 ⟨15,by decide⟩ + (scalarRow12331.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12331.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12331.targetFrame := by
  norm_num [cap12331, scalarRow12331, sourceIndex, cell12331, BstLean.Part263.envelope, parameters]

theorem repair12331Cell16 :
    0 ≤ cap12331 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12331 (parameters ⟨16,by decide⟩)
      (scalarRow12331.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12331 ⟨16,by decide⟩ ∧
    (scalarRow12331.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12331 ⟨16,by decide⟩ + (scalarRow12331.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12331.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12331.targetFrame := by
  norm_num [cap12331, scalarRow12331, sourceIndex, cell12331, BstLean.Part263.envelope, parameters]

theorem repair12331Cell17 :
    0 ≤ cap12331 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12331 (parameters ⟨17,by decide⟩)
      (scalarRow12331.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12331 ⟨17,by decide⟩ ∧
    (scalarRow12331.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12331 ⟨17,by decide⟩ + (scalarRow12331.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12331.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12331.targetFrame := by
  norm_num [cap12331, scalarRow12331, sourceIndex, cell12331, BstLean.Part263.envelope, parameters]

theorem repair12331Cell18 :
    0 ≤ cap12331 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12331 (parameters ⟨18,by decide⟩)
      (scalarRow12331.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12331 ⟨18,by decide⟩ ∧
    (scalarRow12331.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12331 ⟨18,by decide⟩ + (scalarRow12331.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12331.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12331.targetFrame := by
  norm_num [cap12331, scalarRow12331, sourceIndex, cell12331, BstLean.Part263.envelope, parameters]

theorem repair12331Cell19 :
    0 ≤ cap12331 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12331 (parameters ⟨19,by decide⟩)
      (scalarRow12331.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12331 ⟨19,by decide⟩ ∧
    (scalarRow12331.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12331 ⟨19,by decide⟩ + (scalarRow12331.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12331.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12331.targetFrame := by
  norm_num [cap12331, scalarRow12331, sourceIndex, cell12331, BstLean.Part263.envelope, parameters]

theorem repair12331Cell20 :
    0 ≤ cap12331 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12331 (parameters ⟨20,by decide⟩)
      (scalarRow12331.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12331 ⟨20,by decide⟩ ∧
    (scalarRow12331.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12331 ⟨20,by decide⟩ + (scalarRow12331.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12331.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12331.targetFrame := by
  norm_num [cap12331, scalarRow12331, sourceIndex, cell12331, BstLean.Part263.envelope, parameters]

theorem repair12331Cell21 :
    0 ≤ cap12331 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12331 (parameters ⟨21,by decide⟩)
      (scalarRow12331.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12331 ⟨21,by decide⟩ ∧
    (scalarRow12331.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12331 ⟨21,by decide⟩ + (scalarRow12331.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12331.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12331.targetFrame := by
  norm_num [cap12331, scalarRow12331, sourceIndex, cell12331, BstLean.Part263.envelope, parameters]

theorem repair12331Cell22 :
    0 ≤ cap12331 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12331 (parameters ⟨22,by decide⟩)
      (scalarRow12331.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12331 ⟨22,by decide⟩ ∧
    (scalarRow12331.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12331 ⟨22,by decide⟩ + (scalarRow12331.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12331.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12331.targetFrame := by
  norm_num [cap12331, scalarRow12331, sourceIndex, cell12331, BstLean.Part263.envelope, parameters]

theorem repair12331Cell23 :
    0 ≤ cap12331 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12331 (parameters ⟨23,by decide⟩)
      (scalarRow12331.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12331 ⟨23,by decide⟩ ∧
    (scalarRow12331.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12331 ⟨23,by decide⟩ + (scalarRow12331.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12331.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12331.targetFrame := by
  norm_num [cap12331, scalarRow12331, sourceIndex, cell12331, BstLean.Part263.envelope, parameters]

theorem repair12331Cell24 :
    0 ≤ cap12331 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12331 (parameters ⟨24,by decide⟩)
      (scalarRow12331.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12331 ⟨24,by decide⟩ ∧
    (scalarRow12331.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12331 ⟨24,by decide⟩ + (scalarRow12331.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12331.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12331.targetFrame := by
  norm_num [cap12331, scalarRow12331, sourceIndex, cell12331, BstLean.Part263.envelope, parameters]

theorem repair12331Cell25 :
    0 ≤ cap12331 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12331 (parameters ⟨25,by decide⟩)
      (scalarRow12331.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12331 ⟨25,by decide⟩ ∧
    (scalarRow12331.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12331 ⟨25,by decide⟩ + (scalarRow12331.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12331.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12331.targetFrame := by
  norm_num [cap12331, scalarRow12331, sourceIndex, cell12331, BstLean.Part263.envelope, parameters]

theorem repair12331Cell26 :
    0 ≤ cap12331 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12331 (parameters ⟨26,by decide⟩)
      (scalarRow12331.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12331 ⟨26,by decide⟩ ∧
    (scalarRow12331.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12331 ⟨26,by decide⟩ + (scalarRow12331.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12331.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12331.targetFrame := by
  norm_num [cap12331, scalarRow12331, sourceIndex, cell12331, BstLean.Part263.envelope, parameters]

theorem repair12331Cell27 :
    0 ≤ cap12331 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12331 (parameters ⟨27,by decide⟩)
      (scalarRow12331.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12331 ⟨27,by decide⟩ ∧
    (scalarRow12331.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12331 ⟨27,by decide⟩ + (scalarRow12331.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12331.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12331.targetFrame := by
  norm_num [cap12331, scalarRow12331, sourceIndex, cell12331, BstLean.Part263.envelope, parameters]

theorem repair12331Cell28 :
    0 ≤ cap12331 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12331 (parameters ⟨28,by decide⟩)
      (scalarRow12331.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12331 ⟨28,by decide⟩ ∧
    (scalarRow12331.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12331 ⟨28,by decide⟩ + (scalarRow12331.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12331.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12331.targetFrame := by
  norm_num [cap12331, scalarRow12331, sourceIndex, cell12331, BstLean.Part263.envelope, parameters]

theorem repair12331Cell29 :
    0 ≤ cap12331 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12331 (parameters ⟨29,by decide⟩)
      (scalarRow12331.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12331 ⟨29,by decide⟩ ∧
    (scalarRow12331.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12331 ⟨29,by decide⟩ + (scalarRow12331.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12331.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12331.targetFrame := by
  norm_num [cap12331, scalarRow12331, sourceIndex, cell12331, BstLean.Part263.envelope, parameters]

theorem repair12331Cell30 :
    0 ≤ cap12331 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12331 (parameters ⟨30,by decide⟩)
      (scalarRow12331.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12331 ⟨30,by decide⟩ ∧
    (scalarRow12331.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12331 ⟨30,by decide⟩ + (scalarRow12331.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12331.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12331.targetFrame := by
  norm_num [cap12331, scalarRow12331, sourceIndex, cell12331, BstLean.Part263.envelope, parameters]

theorem repair12331Cell31 :
    0 ≤ cap12331 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12331 (parameters ⟨31,by decide⟩)
      (scalarRow12331.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12331 ⟨31,by decide⟩ ∧
    (scalarRow12331.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12331 ⟨31,by decide⟩ + (scalarRow12331.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12331.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12331.targetFrame := by
  norm_num [cap12331, scalarRow12331, sourceIndex, cell12331, BstLean.Part263.envelope, parameters]

theorem repair12331Cell32 :
    0 ≤ cap12331 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12331 (parameters ⟨32,by decide⟩)
      (scalarRow12331.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12331 ⟨32,by decide⟩ ∧
    (scalarRow12331.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12331 ⟨32,by decide⟩ + (scalarRow12331.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12331.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12331.targetFrame := by
  norm_num [cap12331, scalarRow12331, sourceIndex, cell12331, BstLean.Part263.envelope, parameters]

theorem repair12331Cell33 :
    0 ≤ cap12331 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12331 (parameters ⟨33,by decide⟩)
      (scalarRow12331.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12331 ⟨33,by decide⟩ ∧
    (scalarRow12331.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12331 ⟨33,by decide⟩ + (scalarRow12331.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12331.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12331.targetFrame := by
  norm_num [cap12331, scalarRow12331, sourceIndex, cell12331, BstLean.Part263.envelope, parameters]

theorem repair12331Cell34 :
    0 ≤ cap12331 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12331 (parameters ⟨34,by decide⟩)
      (scalarRow12331.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12331 ⟨34,by decide⟩ ∧
    (scalarRow12331.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12331 ⟨34,by decide⟩ + (scalarRow12331.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12331.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12331.targetFrame := by
  norm_num [cap12331, scalarRow12331, sourceIndex, cell12331, BstLean.Part263.envelope, parameters]

theorem repair12331Cell35 :
    0 ≤ cap12331 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12331 (parameters ⟨35,by decide⟩)
      (scalarRow12331.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12331 ⟨35,by decide⟩ ∧
    (scalarRow12331.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12331 ⟨35,by decide⟩ + (scalarRow12331.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12331.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12331.targetFrame := by
  norm_num [cap12331, scalarRow12331, sourceIndex, cell12331, BstLean.Part263.envelope, parameters]

theorem repair12331Cell36 :
    0 ≤ cap12331 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12331 (parameters ⟨36,by decide⟩)
      (scalarRow12331.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12331 ⟨36,by decide⟩ ∧
    (scalarRow12331.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12331 ⟨36,by decide⟩ + (scalarRow12331.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12331.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12331.targetFrame := by
  norm_num [cap12331, scalarRow12331, sourceIndex, cell12331, BstLean.Part263.envelope, parameters]

theorem repair12331Cell37 :
    0 ≤ cap12331 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12331 (parameters ⟨37,by decide⟩)
      (scalarRow12331.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12331 ⟨37,by decide⟩ ∧
    (scalarRow12331.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12331 ⟨37,by decide⟩ + (scalarRow12331.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12331.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12331.targetFrame := by
  norm_num [cap12331, scalarRow12331, sourceIndex, cell12331, BstLean.Part263.envelope, parameters]

theorem repair12331Cell38 :
    0 ≤ cap12331 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12331 (parameters ⟨38,by decide⟩)
      (scalarRow12331.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12331 ⟨38,by decide⟩ ∧
    (scalarRow12331.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12331 ⟨38,by decide⟩ + (scalarRow12331.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12331.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12331.targetFrame := by
  norm_num [cap12331, scalarRow12331, sourceIndex, cell12331, BstLean.Part263.envelope, parameters]

theorem repair12331Cell39 :
    0 ≤ cap12331 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12331 (parameters ⟨39,by decide⟩)
      (scalarRow12331.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12331 ⟨39,by decide⟩ ∧
    (scalarRow12331.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12331 ⟨39,by decide⟩ + (scalarRow12331.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12331.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12331.targetFrame := by
  norm_num [cap12331, scalarRow12331, sourceIndex, cell12331, BstLean.Part263.envelope, parameters]

theorem repair12331Cell40 :
    0 ≤ cap12331 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12331 (parameters ⟨40,by decide⟩)
      (scalarRow12331.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12331 ⟨40,by decide⟩ ∧
    (scalarRow12331.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12331 ⟨40,by decide⟩ + (scalarRow12331.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12331.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12331.targetFrame := by
  norm_num [cap12331, scalarRow12331, sourceIndex, cell12331, BstLean.Part263.envelope, parameters]

theorem repair12331Cell41 :
    0 ≤ cap12331 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12331 (parameters ⟨41,by decide⟩)
      (scalarRow12331.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12331 ⟨41,by decide⟩ ∧
    (scalarRow12331.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12331 ⟨41,by decide⟩ + (scalarRow12331.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12331.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12331.targetFrame := by
  norm_num [cap12331, scalarRow12331, sourceIndex, cell12331, BstLean.Part263.envelope, parameters]

theorem repair12331Cell42 :
    0 ≤ cap12331 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12331 (parameters ⟨42,by decide⟩)
      (scalarRow12331.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12331 ⟨42,by decide⟩ ∧
    (scalarRow12331.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12331 ⟨42,by decide⟩ + (scalarRow12331.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12331.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12331.targetFrame := by
  norm_num [cap12331, scalarRow12331, sourceIndex, cell12331, BstLean.Part263.envelope, parameters]

theorem repair12331Cells (j : Fin 43) :
    0 ≤ cap12331 j ∧
    BstLean.Part263.envelope 12331 (parameters j) (scalarRow12331.table (sourceIndex j)).upper ≤ cap12331 j ∧
    (scalarRow12331.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12331 j + (scalarRow12331.table (sourceIndex j)).centre) /
      (scalarRow12331.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12331.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12331Cell0
  | ⟨1,_⟩ => exact repair12331Cell1
  | ⟨2,_⟩ => exact repair12331Cell2
  | ⟨3,_⟩ => exact repair12331Cell3
  | ⟨4,_⟩ => exact repair12331Cell4
  | ⟨5,_⟩ => exact repair12331Cell5
  | ⟨6,_⟩ => exact repair12331Cell6
  | ⟨7,_⟩ => exact repair12331Cell7
  | ⟨8,_⟩ => exact repair12331Cell8
  | ⟨9,_⟩ => exact repair12331Cell9
  | ⟨10,_⟩ => exact repair12331Cell10
  | ⟨11,_⟩ => exact repair12331Cell11
  | ⟨12,_⟩ => exact repair12331Cell12
  | ⟨13,_⟩ => exact repair12331Cell13
  | ⟨14,_⟩ => exact repair12331Cell14
  | ⟨15,_⟩ => exact repair12331Cell15
  | ⟨16,_⟩ => exact repair12331Cell16
  | ⟨17,_⟩ => exact repair12331Cell17
  | ⟨18,_⟩ => exact repair12331Cell18
  | ⟨19,_⟩ => exact repair12331Cell19
  | ⟨20,_⟩ => exact repair12331Cell20
  | ⟨21,_⟩ => exact repair12331Cell21
  | ⟨22,_⟩ => exact repair12331Cell22
  | ⟨23,_⟩ => exact repair12331Cell23
  | ⟨24,_⟩ => exact repair12331Cell24
  | ⟨25,_⟩ => exact repair12331Cell25
  | ⟨26,_⟩ => exact repair12331Cell26
  | ⟨27,_⟩ => exact repair12331Cell27
  | ⟨28,_⟩ => exact repair12331Cell28
  | ⟨29,_⟩ => exact repair12331Cell29
  | ⟨30,_⟩ => exact repair12331Cell30
  | ⟨31,_⟩ => exact repair12331Cell31
  | ⟨32,_⟩ => exact repair12331Cell32
  | ⟨33,_⟩ => exact repair12331Cell33
  | ⟨34,_⟩ => exact repair12331Cell34
  | ⟨35,_⟩ => exact repair12331Cell35
  | ⟨36,_⟩ => exact repair12331Cell36
  | ⟨37,_⟩ => exact repair12331Cell37
  | ⟨38,_⟩ => exact repair12331Cell38
  | ⟨39,_⟩ => exact repair12331Cell39
  | ⟨40,_⟩ => exact repair12331Cell40
  | ⟨41,_⟩ => exact repair12331Cell41
  | ⟨42,_⟩ => exact repair12331Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12331 : FrameRepair 12331 scalarRow12331 where
  cap := cap12331
  cap_nonneg := fun j => (repair12331Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12331])
  endpoint := fun j => (repair12331Cells j).2.1
  endpoint_upper := fun j => (repair12331Cells j).2.2.1
  frame := fun j => (repair12331Cells j).2.2.2

noncomputable def cap12332 : Fin 43 → ℝ
  | ⟨0,_⟩ => (275944651 / 1000000000 : ℝ)
  | ⟨1,_⟩ => (27634723 / 100000000 : ℝ)
  | ⟨2,_⟩ => (138374407 / 500000000 : ℝ)
  | ⟨3,_⟩ => (138574701 / 500000000 : ℝ)
  | ⟨4,_⟩ => (277549 / 1000000 : ℝ)
  | ⟨5,_⟩ => (34743451 / 125000000 : ℝ)
  | ⟨6,_⟩ => (69586189 / 250000000 : ℝ)
  | ⟨7,_⟩ => (278741399 / 1000000000 : ℝ)
  | ⟨8,_⟩ => (139568533 / 500000000 : ℝ)
  | ⟨9,_⟩ => (139765881 / 500000000 : ℝ)
  | ⟨10,_⟩ => (279925487 / 1000000000 : ℝ)
  | ⟨11,_⟩ => (56063553 / 200000000 : ℝ)
  | ⟨12,_⟩ => (56141913 / 200000000 : ℝ)
  | ⟨13,_⟩ => (281099919 / 1000000000 : ℝ)
  | ⟨14,_⟩ => (281490207 / 1000000000 : ℝ)
  | ⟨15,_⟩ => (56375879 / 200000000 : ℝ)
  | ⟨16,_⟩ => (282267641 / 1000000000 : ℝ)
  | ⟨17,_⟩ => (70663739 / 250000000 : ℝ)
  | ⟨18,_⟩ => (70760333 / 250000000 : ℝ)
  | ⟨19,_⟩ => (283426781 / 1000000000 : ℝ)
  | ⟨20,_⟩ => (283811303 / 1000000000 : ℝ)
  | ⟨21,_⟩ => (284194909 / 1000000000 : ℝ)
  | ⟨22,_⟩ => (35572199 / 125000000 : ℝ)
  | ⟨23,_⟩ => (17809929 / 62500000 : ℝ)
  | ⟨24,_⟩ => (71334931 / 250000000 : ℝ)
  | ⟨25,_⟩ => (35714903 / 125000000 : ℝ)
  | ⟨26,_⟩ => (3576229 / 12500000 : ℝ)
  | ⟨27,_⟩ => (286476017 / 1000000000 : ℝ)
  | ⟨28,_⟩ => (143426409 / 500000000 : ℝ)
  | ⟨29,_⟩ => (287228723 / 1000000000 : ℝ)
  | ⟨30,_⟩ => (71900809 / 250000000 : ℝ)
  | ⟨31,_⟩ => (57595473 / 200000000 : ℝ)
  | ⟨32,_⟩ => (144175307 / 500000000 : ℝ)
  | ⟨33,_⟩ => (36090309 / 125000000 : ℝ)
  | ⟨34,_⟩ => (289093457 / 1000000000 : ℝ)
  | ⟨35,_⟩ => (28946357 / 100000000 : ℝ)
  | ⟨36,_⟩ => (289832807 / 1000000000 : ℝ)
  | ⟨37,_⟩ => (58040237 / 200000000 : ℝ)
  | ⟨38,_⟩ => (145284349 / 500000000 : ℝ)
  | ⟨39,_⟩ => (7273371 / 25000000 : ℝ)
  | ⟨40,_⟩ => (291300123 / 1000000000 : ℝ)
  | ⟨41,_⟩ => (58332911 / 200000000 : ℝ)
  | ⟨42,_⟩ => (36503517 / 125000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12332Cell0 :
    0 ≤ cap12332 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12332 (parameters ⟨0,by decide⟩)
      (scalarRow12332.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12332 ⟨0,by decide⟩ ∧
    (scalarRow12332.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12332 ⟨0,by decide⟩ + (scalarRow12332.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12332.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12332.targetFrame := by
  norm_num [cap12332, scalarRow12332, sourceIndex, cell12332, BstLean.Part263.envelope, parameters]

theorem repair12332Cell1 :
    0 ≤ cap12332 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12332 (parameters ⟨1,by decide⟩)
      (scalarRow12332.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12332 ⟨1,by decide⟩ ∧
    (scalarRow12332.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12332 ⟨1,by decide⟩ + (scalarRow12332.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12332.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12332.targetFrame := by
  norm_num [cap12332, scalarRow12332, sourceIndex, cell12332, BstLean.Part263.envelope, parameters]

theorem repair12332Cell2 :
    0 ≤ cap12332 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12332 (parameters ⟨2,by decide⟩)
      (scalarRow12332.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12332 ⟨2,by decide⟩ ∧
    (scalarRow12332.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12332 ⟨2,by decide⟩ + (scalarRow12332.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12332.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12332.targetFrame := by
  norm_num [cap12332, scalarRow12332, sourceIndex, cell12332, BstLean.Part263.envelope, parameters]

theorem repair12332Cell3 :
    0 ≤ cap12332 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12332 (parameters ⟨3,by decide⟩)
      (scalarRow12332.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12332 ⟨3,by decide⟩ ∧
    (scalarRow12332.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12332 ⟨3,by decide⟩ + (scalarRow12332.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12332.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12332.targetFrame := by
  norm_num [cap12332, scalarRow12332, sourceIndex, cell12332, BstLean.Part263.envelope, parameters]

theorem repair12332Cell4 :
    0 ≤ cap12332 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12332 (parameters ⟨4,by decide⟩)
      (scalarRow12332.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12332 ⟨4,by decide⟩ ∧
    (scalarRow12332.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12332 ⟨4,by decide⟩ + (scalarRow12332.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12332.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12332.targetFrame := by
  norm_num [cap12332, scalarRow12332, sourceIndex, cell12332, BstLean.Part263.envelope, parameters]

theorem repair12332Cell5 :
    0 ≤ cap12332 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12332 (parameters ⟨5,by decide⟩)
      (scalarRow12332.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12332 ⟨5,by decide⟩ ∧
    (scalarRow12332.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12332 ⟨5,by decide⟩ + (scalarRow12332.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12332.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12332.targetFrame := by
  norm_num [cap12332, scalarRow12332, sourceIndex, cell12332, BstLean.Part263.envelope, parameters]

theorem repair12332Cell6 :
    0 ≤ cap12332 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12332 (parameters ⟨6,by decide⟩)
      (scalarRow12332.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12332 ⟨6,by decide⟩ ∧
    (scalarRow12332.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12332 ⟨6,by decide⟩ + (scalarRow12332.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12332.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12332.targetFrame := by
  norm_num [cap12332, scalarRow12332, sourceIndex, cell12332, BstLean.Part263.envelope, parameters]

theorem repair12332Cell7 :
    0 ≤ cap12332 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12332 (parameters ⟨7,by decide⟩)
      (scalarRow12332.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12332 ⟨7,by decide⟩ ∧
    (scalarRow12332.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12332 ⟨7,by decide⟩ + (scalarRow12332.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12332.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12332.targetFrame := by
  norm_num [cap12332, scalarRow12332, sourceIndex, cell12332, BstLean.Part263.envelope, parameters]

theorem repair12332Cell8 :
    0 ≤ cap12332 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12332 (parameters ⟨8,by decide⟩)
      (scalarRow12332.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12332 ⟨8,by decide⟩ ∧
    (scalarRow12332.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12332 ⟨8,by decide⟩ + (scalarRow12332.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12332.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12332.targetFrame := by
  norm_num [cap12332, scalarRow12332, sourceIndex, cell12332, BstLean.Part263.envelope, parameters]

theorem repair12332Cell9 :
    0 ≤ cap12332 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12332 (parameters ⟨9,by decide⟩)
      (scalarRow12332.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12332 ⟨9,by decide⟩ ∧
    (scalarRow12332.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12332 ⟨9,by decide⟩ + (scalarRow12332.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12332.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12332.targetFrame := by
  norm_num [cap12332, scalarRow12332, sourceIndex, cell12332, BstLean.Part263.envelope, parameters]

theorem repair12332Cell10 :
    0 ≤ cap12332 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12332 (parameters ⟨10,by decide⟩)
      (scalarRow12332.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12332 ⟨10,by decide⟩ ∧
    (scalarRow12332.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12332 ⟨10,by decide⟩ + (scalarRow12332.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12332.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12332.targetFrame := by
  norm_num [cap12332, scalarRow12332, sourceIndex, cell12332, BstLean.Part263.envelope, parameters]

theorem repair12332Cell11 :
    0 ≤ cap12332 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12332 (parameters ⟨11,by decide⟩)
      (scalarRow12332.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12332 ⟨11,by decide⟩ ∧
    (scalarRow12332.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12332 ⟨11,by decide⟩ + (scalarRow12332.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12332.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12332.targetFrame := by
  norm_num [cap12332, scalarRow12332, sourceIndex, cell12332, BstLean.Part263.envelope, parameters]

theorem repair12332Cell12 :
    0 ≤ cap12332 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12332 (parameters ⟨12,by decide⟩)
      (scalarRow12332.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12332 ⟨12,by decide⟩ ∧
    (scalarRow12332.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12332 ⟨12,by decide⟩ + (scalarRow12332.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12332.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12332.targetFrame := by
  norm_num [cap12332, scalarRow12332, sourceIndex, cell12332, BstLean.Part263.envelope, parameters]

theorem repair12332Cell13 :
    0 ≤ cap12332 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12332 (parameters ⟨13,by decide⟩)
      (scalarRow12332.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12332 ⟨13,by decide⟩ ∧
    (scalarRow12332.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12332 ⟨13,by decide⟩ + (scalarRow12332.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12332.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12332.targetFrame := by
  norm_num [cap12332, scalarRow12332, sourceIndex, cell12332, BstLean.Part263.envelope, parameters]

theorem repair12332Cell14 :
    0 ≤ cap12332 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12332 (parameters ⟨14,by decide⟩)
      (scalarRow12332.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12332 ⟨14,by decide⟩ ∧
    (scalarRow12332.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12332 ⟨14,by decide⟩ + (scalarRow12332.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12332.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12332.targetFrame := by
  norm_num [cap12332, scalarRow12332, sourceIndex, cell12332, BstLean.Part263.envelope, parameters]

theorem repair12332Cell15 :
    0 ≤ cap12332 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12332 (parameters ⟨15,by decide⟩)
      (scalarRow12332.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12332 ⟨15,by decide⟩ ∧
    (scalarRow12332.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12332 ⟨15,by decide⟩ + (scalarRow12332.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12332.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12332.targetFrame := by
  norm_num [cap12332, scalarRow12332, sourceIndex, cell12332, BstLean.Part263.envelope, parameters]

theorem repair12332Cell16 :
    0 ≤ cap12332 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12332 (parameters ⟨16,by decide⟩)
      (scalarRow12332.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12332 ⟨16,by decide⟩ ∧
    (scalarRow12332.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12332 ⟨16,by decide⟩ + (scalarRow12332.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12332.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12332.targetFrame := by
  norm_num [cap12332, scalarRow12332, sourceIndex, cell12332, BstLean.Part263.envelope, parameters]

theorem repair12332Cell17 :
    0 ≤ cap12332 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12332 (parameters ⟨17,by decide⟩)
      (scalarRow12332.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12332 ⟨17,by decide⟩ ∧
    (scalarRow12332.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12332 ⟨17,by decide⟩ + (scalarRow12332.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12332.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12332.targetFrame := by
  norm_num [cap12332, scalarRow12332, sourceIndex, cell12332, BstLean.Part263.envelope, parameters]

theorem repair12332Cell18 :
    0 ≤ cap12332 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12332 (parameters ⟨18,by decide⟩)
      (scalarRow12332.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12332 ⟨18,by decide⟩ ∧
    (scalarRow12332.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12332 ⟨18,by decide⟩ + (scalarRow12332.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12332.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12332.targetFrame := by
  norm_num [cap12332, scalarRow12332, sourceIndex, cell12332, BstLean.Part263.envelope, parameters]

theorem repair12332Cell19 :
    0 ≤ cap12332 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12332 (parameters ⟨19,by decide⟩)
      (scalarRow12332.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12332 ⟨19,by decide⟩ ∧
    (scalarRow12332.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12332 ⟨19,by decide⟩ + (scalarRow12332.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12332.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12332.targetFrame := by
  norm_num [cap12332, scalarRow12332, sourceIndex, cell12332, BstLean.Part263.envelope, parameters]

theorem repair12332Cell20 :
    0 ≤ cap12332 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12332 (parameters ⟨20,by decide⟩)
      (scalarRow12332.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12332 ⟨20,by decide⟩ ∧
    (scalarRow12332.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12332 ⟨20,by decide⟩ + (scalarRow12332.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12332.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12332.targetFrame := by
  norm_num [cap12332, scalarRow12332, sourceIndex, cell12332, BstLean.Part263.envelope, parameters]

theorem repair12332Cell21 :
    0 ≤ cap12332 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12332 (parameters ⟨21,by decide⟩)
      (scalarRow12332.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12332 ⟨21,by decide⟩ ∧
    (scalarRow12332.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12332 ⟨21,by decide⟩ + (scalarRow12332.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12332.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12332.targetFrame := by
  norm_num [cap12332, scalarRow12332, sourceIndex, cell12332, BstLean.Part263.envelope, parameters]

theorem repair12332Cell22 :
    0 ≤ cap12332 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12332 (parameters ⟨22,by decide⟩)
      (scalarRow12332.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12332 ⟨22,by decide⟩ ∧
    (scalarRow12332.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12332 ⟨22,by decide⟩ + (scalarRow12332.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12332.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12332.targetFrame := by
  norm_num [cap12332, scalarRow12332, sourceIndex, cell12332, BstLean.Part263.envelope, parameters]

theorem repair12332Cell23 :
    0 ≤ cap12332 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12332 (parameters ⟨23,by decide⟩)
      (scalarRow12332.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12332 ⟨23,by decide⟩ ∧
    (scalarRow12332.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12332 ⟨23,by decide⟩ + (scalarRow12332.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12332.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12332.targetFrame := by
  norm_num [cap12332, scalarRow12332, sourceIndex, cell12332, BstLean.Part263.envelope, parameters]

theorem repair12332Cell24 :
    0 ≤ cap12332 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12332 (parameters ⟨24,by decide⟩)
      (scalarRow12332.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12332 ⟨24,by decide⟩ ∧
    (scalarRow12332.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12332 ⟨24,by decide⟩ + (scalarRow12332.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12332.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12332.targetFrame := by
  norm_num [cap12332, scalarRow12332, sourceIndex, cell12332, BstLean.Part263.envelope, parameters]

theorem repair12332Cell25 :
    0 ≤ cap12332 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12332 (parameters ⟨25,by decide⟩)
      (scalarRow12332.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12332 ⟨25,by decide⟩ ∧
    (scalarRow12332.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12332 ⟨25,by decide⟩ + (scalarRow12332.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12332.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12332.targetFrame := by
  norm_num [cap12332, scalarRow12332, sourceIndex, cell12332, BstLean.Part263.envelope, parameters]

theorem repair12332Cell26 :
    0 ≤ cap12332 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12332 (parameters ⟨26,by decide⟩)
      (scalarRow12332.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12332 ⟨26,by decide⟩ ∧
    (scalarRow12332.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12332 ⟨26,by decide⟩ + (scalarRow12332.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12332.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12332.targetFrame := by
  norm_num [cap12332, scalarRow12332, sourceIndex, cell12332, BstLean.Part263.envelope, parameters]

theorem repair12332Cell27 :
    0 ≤ cap12332 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12332 (parameters ⟨27,by decide⟩)
      (scalarRow12332.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12332 ⟨27,by decide⟩ ∧
    (scalarRow12332.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12332 ⟨27,by decide⟩ + (scalarRow12332.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12332.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12332.targetFrame := by
  norm_num [cap12332, scalarRow12332, sourceIndex, cell12332, BstLean.Part263.envelope, parameters]

theorem repair12332Cell28 :
    0 ≤ cap12332 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12332 (parameters ⟨28,by decide⟩)
      (scalarRow12332.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12332 ⟨28,by decide⟩ ∧
    (scalarRow12332.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12332 ⟨28,by decide⟩ + (scalarRow12332.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12332.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12332.targetFrame := by
  norm_num [cap12332, scalarRow12332, sourceIndex, cell12332, BstLean.Part263.envelope, parameters]

theorem repair12332Cell29 :
    0 ≤ cap12332 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12332 (parameters ⟨29,by decide⟩)
      (scalarRow12332.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12332 ⟨29,by decide⟩ ∧
    (scalarRow12332.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12332 ⟨29,by decide⟩ + (scalarRow12332.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12332.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12332.targetFrame := by
  norm_num [cap12332, scalarRow12332, sourceIndex, cell12332, BstLean.Part263.envelope, parameters]

theorem repair12332Cell30 :
    0 ≤ cap12332 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12332 (parameters ⟨30,by decide⟩)
      (scalarRow12332.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12332 ⟨30,by decide⟩ ∧
    (scalarRow12332.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12332 ⟨30,by decide⟩ + (scalarRow12332.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12332.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12332.targetFrame := by
  norm_num [cap12332, scalarRow12332, sourceIndex, cell12332, BstLean.Part263.envelope, parameters]

theorem repair12332Cell31 :
    0 ≤ cap12332 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12332 (parameters ⟨31,by decide⟩)
      (scalarRow12332.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12332 ⟨31,by decide⟩ ∧
    (scalarRow12332.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12332 ⟨31,by decide⟩ + (scalarRow12332.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12332.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12332.targetFrame := by
  norm_num [cap12332, scalarRow12332, sourceIndex, cell12332, BstLean.Part263.envelope, parameters]

theorem repair12332Cell32 :
    0 ≤ cap12332 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12332 (parameters ⟨32,by decide⟩)
      (scalarRow12332.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12332 ⟨32,by decide⟩ ∧
    (scalarRow12332.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12332 ⟨32,by decide⟩ + (scalarRow12332.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12332.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12332.targetFrame := by
  norm_num [cap12332, scalarRow12332, sourceIndex, cell12332, BstLean.Part263.envelope, parameters]

theorem repair12332Cell33 :
    0 ≤ cap12332 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12332 (parameters ⟨33,by decide⟩)
      (scalarRow12332.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12332 ⟨33,by decide⟩ ∧
    (scalarRow12332.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12332 ⟨33,by decide⟩ + (scalarRow12332.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12332.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12332.targetFrame := by
  norm_num [cap12332, scalarRow12332, sourceIndex, cell12332, BstLean.Part263.envelope, parameters]

theorem repair12332Cell34 :
    0 ≤ cap12332 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12332 (parameters ⟨34,by decide⟩)
      (scalarRow12332.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12332 ⟨34,by decide⟩ ∧
    (scalarRow12332.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12332 ⟨34,by decide⟩ + (scalarRow12332.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12332.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12332.targetFrame := by
  norm_num [cap12332, scalarRow12332, sourceIndex, cell12332, BstLean.Part263.envelope, parameters]

theorem repair12332Cell35 :
    0 ≤ cap12332 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12332 (parameters ⟨35,by decide⟩)
      (scalarRow12332.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12332 ⟨35,by decide⟩ ∧
    (scalarRow12332.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12332 ⟨35,by decide⟩ + (scalarRow12332.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12332.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12332.targetFrame := by
  norm_num [cap12332, scalarRow12332, sourceIndex, cell12332, BstLean.Part263.envelope, parameters]

theorem repair12332Cell36 :
    0 ≤ cap12332 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12332 (parameters ⟨36,by decide⟩)
      (scalarRow12332.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12332 ⟨36,by decide⟩ ∧
    (scalarRow12332.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12332 ⟨36,by decide⟩ + (scalarRow12332.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12332.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12332.targetFrame := by
  norm_num [cap12332, scalarRow12332, sourceIndex, cell12332, BstLean.Part263.envelope, parameters]

theorem repair12332Cell37 :
    0 ≤ cap12332 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12332 (parameters ⟨37,by decide⟩)
      (scalarRow12332.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12332 ⟨37,by decide⟩ ∧
    (scalarRow12332.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12332 ⟨37,by decide⟩ + (scalarRow12332.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12332.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12332.targetFrame := by
  norm_num [cap12332, scalarRow12332, sourceIndex, cell12332, BstLean.Part263.envelope, parameters]

theorem repair12332Cell38 :
    0 ≤ cap12332 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12332 (parameters ⟨38,by decide⟩)
      (scalarRow12332.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12332 ⟨38,by decide⟩ ∧
    (scalarRow12332.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12332 ⟨38,by decide⟩ + (scalarRow12332.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12332.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12332.targetFrame := by
  norm_num [cap12332, scalarRow12332, sourceIndex, cell12332, BstLean.Part263.envelope, parameters]

theorem repair12332Cell39 :
    0 ≤ cap12332 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12332 (parameters ⟨39,by decide⟩)
      (scalarRow12332.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12332 ⟨39,by decide⟩ ∧
    (scalarRow12332.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12332 ⟨39,by decide⟩ + (scalarRow12332.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12332.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12332.targetFrame := by
  norm_num [cap12332, scalarRow12332, sourceIndex, cell12332, BstLean.Part263.envelope, parameters]

theorem repair12332Cell40 :
    0 ≤ cap12332 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12332 (parameters ⟨40,by decide⟩)
      (scalarRow12332.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12332 ⟨40,by decide⟩ ∧
    (scalarRow12332.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12332 ⟨40,by decide⟩ + (scalarRow12332.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12332.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12332.targetFrame := by
  norm_num [cap12332, scalarRow12332, sourceIndex, cell12332, BstLean.Part263.envelope, parameters]

theorem repair12332Cell41 :
    0 ≤ cap12332 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12332 (parameters ⟨41,by decide⟩)
      (scalarRow12332.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12332 ⟨41,by decide⟩ ∧
    (scalarRow12332.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12332 ⟨41,by decide⟩ + (scalarRow12332.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12332.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12332.targetFrame := by
  norm_num [cap12332, scalarRow12332, sourceIndex, cell12332, BstLean.Part263.envelope, parameters]

theorem repair12332Cell42 :
    0 ≤ cap12332 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12332 (parameters ⟨42,by decide⟩)
      (scalarRow12332.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12332 ⟨42,by decide⟩ ∧
    (scalarRow12332.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12332 ⟨42,by decide⟩ + (scalarRow12332.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12332.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12332.targetFrame := by
  norm_num [cap12332, scalarRow12332, sourceIndex, cell12332, BstLean.Part263.envelope, parameters]

theorem repair12332Cells (j : Fin 43) :
    0 ≤ cap12332 j ∧
    BstLean.Part263.envelope 12332 (parameters j) (scalarRow12332.table (sourceIndex j)).upper ≤ cap12332 j ∧
    (scalarRow12332.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12332 j + (scalarRow12332.table (sourceIndex j)).centre) /
      (scalarRow12332.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12332.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12332Cell0
  | ⟨1,_⟩ => exact repair12332Cell1
  | ⟨2,_⟩ => exact repair12332Cell2
  | ⟨3,_⟩ => exact repair12332Cell3
  | ⟨4,_⟩ => exact repair12332Cell4
  | ⟨5,_⟩ => exact repair12332Cell5
  | ⟨6,_⟩ => exact repair12332Cell6
  | ⟨7,_⟩ => exact repair12332Cell7
  | ⟨8,_⟩ => exact repair12332Cell8
  | ⟨9,_⟩ => exact repair12332Cell9
  | ⟨10,_⟩ => exact repair12332Cell10
  | ⟨11,_⟩ => exact repair12332Cell11
  | ⟨12,_⟩ => exact repair12332Cell12
  | ⟨13,_⟩ => exact repair12332Cell13
  | ⟨14,_⟩ => exact repair12332Cell14
  | ⟨15,_⟩ => exact repair12332Cell15
  | ⟨16,_⟩ => exact repair12332Cell16
  | ⟨17,_⟩ => exact repair12332Cell17
  | ⟨18,_⟩ => exact repair12332Cell18
  | ⟨19,_⟩ => exact repair12332Cell19
  | ⟨20,_⟩ => exact repair12332Cell20
  | ⟨21,_⟩ => exact repair12332Cell21
  | ⟨22,_⟩ => exact repair12332Cell22
  | ⟨23,_⟩ => exact repair12332Cell23
  | ⟨24,_⟩ => exact repair12332Cell24
  | ⟨25,_⟩ => exact repair12332Cell25
  | ⟨26,_⟩ => exact repair12332Cell26
  | ⟨27,_⟩ => exact repair12332Cell27
  | ⟨28,_⟩ => exact repair12332Cell28
  | ⟨29,_⟩ => exact repair12332Cell29
  | ⟨30,_⟩ => exact repair12332Cell30
  | ⟨31,_⟩ => exact repair12332Cell31
  | ⟨32,_⟩ => exact repair12332Cell32
  | ⟨33,_⟩ => exact repair12332Cell33
  | ⟨34,_⟩ => exact repair12332Cell34
  | ⟨35,_⟩ => exact repair12332Cell35
  | ⟨36,_⟩ => exact repair12332Cell36
  | ⟨37,_⟩ => exact repair12332Cell37
  | ⟨38,_⟩ => exact repair12332Cell38
  | ⟨39,_⟩ => exact repair12332Cell39
  | ⟨40,_⟩ => exact repair12332Cell40
  | ⟨41,_⟩ => exact repair12332Cell41
  | ⟨42,_⟩ => exact repair12332Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12332 : FrameRepair 12332 scalarRow12332 where
  cap := cap12332
  cap_nonneg := fun j => (repair12332Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12332])
  endpoint := fun j => (repair12332Cells j).2.1
  endpoint_upper := fun j => (repair12332Cells j).2.2.1
  frame := fun j => (repair12332Cells j).2.2.2

noncomputable def cap12333 : Fin 43 → ℝ
  | ⟨0,_⟩ => (2155817 / 7812500 : ℝ)
  | ⟨1,_⟩ => (69086787 / 250000000 : ℝ)
  | ⟨2,_⟩ => (138374363 / 500000000 : ℝ)
  | ⟨3,_⟩ => (69287327 / 250000000 : ℝ)
  | ⟨4,_⟩ => (277548899 / 1000000000 : ℝ)
  | ⟨5,_⟩ => (277947501 / 1000000000 : ℝ)
  | ⟨6,_⟩ => (278344643 / 1000000000 : ℝ)
  | ⟨7,_⟩ => (278741279 / 1000000000 : ℝ)
  | ⟨8,_⟩ => (13956847 / 50000000 : ℝ)
  | ⟨9,_⟩ => (27953163 / 100000000 : ℝ)
  | ⟨10,_⟩ => (69981337 / 250000000 : ℝ)
  | ⟨11,_⟩ => (14015881 / 50000000 : ℝ)
  | ⟨12,_⟩ => (140354707 / 500000000 : ℝ)
  | ⟨13,_⟩ => (281099761 / 1000000000 : ℝ)
  | ⟨14,_⟩ => (281490043 / 1000000000 : ℝ)
  | ⟨15,_⟩ => (11275169 / 40000000 : ℝ)
  | ⟨16,_⟩ => (35283433 / 125000000 : ℝ)
  | ⟨17,_⟩ => (282654773 / 1000000000 : ℝ)
  | ⟨18,_⟩ => (35380143 / 125000000 : ℝ)
  | ⟨19,_⟩ => (141713293 / 500000000 : ℝ)
  | ⟨20,_⟩ => (141905551 / 500000000 : ℝ)
  | ⟨21,_⟩ => (284194701 / 1000000000 : ℝ)
  | ⟨22,_⟩ => (142288689 / 500000000 : ℝ)
  | ⟨23,_⟩ => (71239661 / 250000000 : ℝ)
  | ⟨24,_⟩ => (142669749 / 500000000 : ℝ)
  | ⟨25,_⟩ => (17857437 / 62500000 : ℝ)
  | ⟨26,_⟩ => (143049041 / 500000000 : ℝ)
  | ⟨27,_⟩ => (71618943 / 250000000 : ℝ)
  | ⟨28,_⟩ => (286852567 / 1000000000 : ℝ)
  | ⟨29,_⟩ => (287228467 / 1000000000 : ℝ)
  | ⟨30,_⟩ => (143801487 / 500000000 : ℝ)
  | ⟨31,_⟩ => (287977097 / 1000000000 : ℝ)
  | ⟨32,_⟩ => (288350339 / 1000000000 : ℝ)
  | ⟨33,_⟩ => (18045137 / 62500000 : ℝ)
  | ⟨34,_⟩ => (28909317 / 100000000 : ℝ)
  | ⟨35,_⟩ => (289463277 / 1000000000 : ℝ)
  | ⟨36,_⟩ => (72458127 / 250000000 : ℝ)
  | ⟨37,_⟩ => (3627511 / 12500000 : ℝ)
  | ⟨38,_⟩ => (72642097 / 250000000 : ℝ)
  | ⟨39,_⟩ => (290934523 / 1000000000 : ℝ)
  | ⟨40,_⟩ => (291299801 / 1000000000 : ℝ)
  | ⟨41,_⟩ => (291664227 / 1000000000 : ℝ)
  | ⟨42,_⟩ => (146013901 / 500000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12333Cell0 :
    0 ≤ cap12333 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12333 (parameters ⟨0,by decide⟩)
      (scalarRow12333.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12333 ⟨0,by decide⟩ ∧
    (scalarRow12333.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12333 ⟨0,by decide⟩ + (scalarRow12333.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12333.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12333.targetFrame := by
  norm_num [cap12333, scalarRow12333, sourceIndex, cell12333, BstLean.Part263.envelope, parameters]

theorem repair12333Cell1 :
    0 ≤ cap12333 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12333 (parameters ⟨1,by decide⟩)
      (scalarRow12333.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12333 ⟨1,by decide⟩ ∧
    (scalarRow12333.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12333 ⟨1,by decide⟩ + (scalarRow12333.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12333.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12333.targetFrame := by
  norm_num [cap12333, scalarRow12333, sourceIndex, cell12333, BstLean.Part263.envelope, parameters]

theorem repair12333Cell2 :
    0 ≤ cap12333 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12333 (parameters ⟨2,by decide⟩)
      (scalarRow12333.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12333 ⟨2,by decide⟩ ∧
    (scalarRow12333.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12333 ⟨2,by decide⟩ + (scalarRow12333.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12333.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12333.targetFrame := by
  norm_num [cap12333, scalarRow12333, sourceIndex, cell12333, BstLean.Part263.envelope, parameters]

theorem repair12333Cell3 :
    0 ≤ cap12333 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12333 (parameters ⟨3,by decide⟩)
      (scalarRow12333.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12333 ⟨3,by decide⟩ ∧
    (scalarRow12333.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12333 ⟨3,by decide⟩ + (scalarRow12333.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12333.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12333.targetFrame := by
  norm_num [cap12333, scalarRow12333, sourceIndex, cell12333, BstLean.Part263.envelope, parameters]

theorem repair12333Cell4 :
    0 ≤ cap12333 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12333 (parameters ⟨4,by decide⟩)
      (scalarRow12333.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12333 ⟨4,by decide⟩ ∧
    (scalarRow12333.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12333 ⟨4,by decide⟩ + (scalarRow12333.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12333.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12333.targetFrame := by
  norm_num [cap12333, scalarRow12333, sourceIndex, cell12333, BstLean.Part263.envelope, parameters]

theorem repair12333Cell5 :
    0 ≤ cap12333 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12333 (parameters ⟨5,by decide⟩)
      (scalarRow12333.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12333 ⟨5,by decide⟩ ∧
    (scalarRow12333.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12333 ⟨5,by decide⟩ + (scalarRow12333.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12333.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12333.targetFrame := by
  norm_num [cap12333, scalarRow12333, sourceIndex, cell12333, BstLean.Part263.envelope, parameters]

theorem repair12333Cell6 :
    0 ≤ cap12333 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12333 (parameters ⟨6,by decide⟩)
      (scalarRow12333.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12333 ⟨6,by decide⟩ ∧
    (scalarRow12333.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12333 ⟨6,by decide⟩ + (scalarRow12333.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12333.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12333.targetFrame := by
  norm_num [cap12333, scalarRow12333, sourceIndex, cell12333, BstLean.Part263.envelope, parameters]

theorem repair12333Cell7 :
    0 ≤ cap12333 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12333 (parameters ⟨7,by decide⟩)
      (scalarRow12333.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12333 ⟨7,by decide⟩ ∧
    (scalarRow12333.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12333 ⟨7,by decide⟩ + (scalarRow12333.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12333.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12333.targetFrame := by
  norm_num [cap12333, scalarRow12333, sourceIndex, cell12333, BstLean.Part263.envelope, parameters]

theorem repair12333Cell8 :
    0 ≤ cap12333 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12333 (parameters ⟨8,by decide⟩)
      (scalarRow12333.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12333 ⟨8,by decide⟩ ∧
    (scalarRow12333.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12333 ⟨8,by decide⟩ + (scalarRow12333.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12333.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12333.targetFrame := by
  norm_num [cap12333, scalarRow12333, sourceIndex, cell12333, BstLean.Part263.envelope, parameters]

theorem repair12333Cell9 :
    0 ≤ cap12333 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12333 (parameters ⟨9,by decide⟩)
      (scalarRow12333.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12333 ⟨9,by decide⟩ ∧
    (scalarRow12333.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12333 ⟨9,by decide⟩ + (scalarRow12333.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12333.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12333.targetFrame := by
  norm_num [cap12333, scalarRow12333, sourceIndex, cell12333, BstLean.Part263.envelope, parameters]

theorem repair12333Cell10 :
    0 ≤ cap12333 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12333 (parameters ⟨10,by decide⟩)
      (scalarRow12333.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12333 ⟨10,by decide⟩ ∧
    (scalarRow12333.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12333 ⟨10,by decide⟩ + (scalarRow12333.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12333.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12333.targetFrame := by
  norm_num [cap12333, scalarRow12333, sourceIndex, cell12333, BstLean.Part263.envelope, parameters]

theorem repair12333Cell11 :
    0 ≤ cap12333 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12333 (parameters ⟨11,by decide⟩)
      (scalarRow12333.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12333 ⟨11,by decide⟩ ∧
    (scalarRow12333.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12333 ⟨11,by decide⟩ + (scalarRow12333.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12333.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12333.targetFrame := by
  norm_num [cap12333, scalarRow12333, sourceIndex, cell12333, BstLean.Part263.envelope, parameters]

theorem repair12333Cell12 :
    0 ≤ cap12333 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12333 (parameters ⟨12,by decide⟩)
      (scalarRow12333.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12333 ⟨12,by decide⟩ ∧
    (scalarRow12333.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12333 ⟨12,by decide⟩ + (scalarRow12333.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12333.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12333.targetFrame := by
  norm_num [cap12333, scalarRow12333, sourceIndex, cell12333, BstLean.Part263.envelope, parameters]

theorem repair12333Cell13 :
    0 ≤ cap12333 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12333 (parameters ⟨13,by decide⟩)
      (scalarRow12333.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12333 ⟨13,by decide⟩ ∧
    (scalarRow12333.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12333 ⟨13,by decide⟩ + (scalarRow12333.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12333.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12333.targetFrame := by
  norm_num [cap12333, scalarRow12333, sourceIndex, cell12333, BstLean.Part263.envelope, parameters]

theorem repair12333Cell14 :
    0 ≤ cap12333 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12333 (parameters ⟨14,by decide⟩)
      (scalarRow12333.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12333 ⟨14,by decide⟩ ∧
    (scalarRow12333.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12333 ⟨14,by decide⟩ + (scalarRow12333.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12333.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12333.targetFrame := by
  norm_num [cap12333, scalarRow12333, sourceIndex, cell12333, BstLean.Part263.envelope, parameters]

theorem repair12333Cell15 :
    0 ≤ cap12333 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12333 (parameters ⟨15,by decide⟩)
      (scalarRow12333.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12333 ⟨15,by decide⟩ ∧
    (scalarRow12333.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12333 ⟨15,by decide⟩ + (scalarRow12333.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12333.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12333.targetFrame := by
  norm_num [cap12333, scalarRow12333, sourceIndex, cell12333, BstLean.Part263.envelope, parameters]

theorem repair12333Cell16 :
    0 ≤ cap12333 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12333 (parameters ⟨16,by decide⟩)
      (scalarRow12333.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12333 ⟨16,by decide⟩ ∧
    (scalarRow12333.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12333 ⟨16,by decide⟩ + (scalarRow12333.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12333.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12333.targetFrame := by
  norm_num [cap12333, scalarRow12333, sourceIndex, cell12333, BstLean.Part263.envelope, parameters]

theorem repair12333Cell17 :
    0 ≤ cap12333 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12333 (parameters ⟨17,by decide⟩)
      (scalarRow12333.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12333 ⟨17,by decide⟩ ∧
    (scalarRow12333.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12333 ⟨17,by decide⟩ + (scalarRow12333.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12333.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12333.targetFrame := by
  norm_num [cap12333, scalarRow12333, sourceIndex, cell12333, BstLean.Part263.envelope, parameters]

theorem repair12333Cell18 :
    0 ≤ cap12333 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12333 (parameters ⟨18,by decide⟩)
      (scalarRow12333.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12333 ⟨18,by decide⟩ ∧
    (scalarRow12333.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12333 ⟨18,by decide⟩ + (scalarRow12333.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12333.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12333.targetFrame := by
  norm_num [cap12333, scalarRow12333, sourceIndex, cell12333, BstLean.Part263.envelope, parameters]

theorem repair12333Cell19 :
    0 ≤ cap12333 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12333 (parameters ⟨19,by decide⟩)
      (scalarRow12333.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12333 ⟨19,by decide⟩ ∧
    (scalarRow12333.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12333 ⟨19,by decide⟩ + (scalarRow12333.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12333.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12333.targetFrame := by
  norm_num [cap12333, scalarRow12333, sourceIndex, cell12333, BstLean.Part263.envelope, parameters]

theorem repair12333Cell20 :
    0 ≤ cap12333 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12333 (parameters ⟨20,by decide⟩)
      (scalarRow12333.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12333 ⟨20,by decide⟩ ∧
    (scalarRow12333.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12333 ⟨20,by decide⟩ + (scalarRow12333.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12333.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12333.targetFrame := by
  norm_num [cap12333, scalarRow12333, sourceIndex, cell12333, BstLean.Part263.envelope, parameters]

theorem repair12333Cell21 :
    0 ≤ cap12333 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12333 (parameters ⟨21,by decide⟩)
      (scalarRow12333.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12333 ⟨21,by decide⟩ ∧
    (scalarRow12333.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12333 ⟨21,by decide⟩ + (scalarRow12333.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12333.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12333.targetFrame := by
  norm_num [cap12333, scalarRow12333, sourceIndex, cell12333, BstLean.Part263.envelope, parameters]

theorem repair12333Cell22 :
    0 ≤ cap12333 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12333 (parameters ⟨22,by decide⟩)
      (scalarRow12333.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12333 ⟨22,by decide⟩ ∧
    (scalarRow12333.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12333 ⟨22,by decide⟩ + (scalarRow12333.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12333.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12333.targetFrame := by
  norm_num [cap12333, scalarRow12333, sourceIndex, cell12333, BstLean.Part263.envelope, parameters]

theorem repair12333Cell23 :
    0 ≤ cap12333 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12333 (parameters ⟨23,by decide⟩)
      (scalarRow12333.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12333 ⟨23,by decide⟩ ∧
    (scalarRow12333.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12333 ⟨23,by decide⟩ + (scalarRow12333.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12333.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12333.targetFrame := by
  norm_num [cap12333, scalarRow12333, sourceIndex, cell12333, BstLean.Part263.envelope, parameters]

theorem repair12333Cell24 :
    0 ≤ cap12333 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12333 (parameters ⟨24,by decide⟩)
      (scalarRow12333.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12333 ⟨24,by decide⟩ ∧
    (scalarRow12333.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12333 ⟨24,by decide⟩ + (scalarRow12333.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12333.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12333.targetFrame := by
  norm_num [cap12333, scalarRow12333, sourceIndex, cell12333, BstLean.Part263.envelope, parameters]

theorem repair12333Cell25 :
    0 ≤ cap12333 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12333 (parameters ⟨25,by decide⟩)
      (scalarRow12333.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12333 ⟨25,by decide⟩ ∧
    (scalarRow12333.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12333 ⟨25,by decide⟩ + (scalarRow12333.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12333.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12333.targetFrame := by
  norm_num [cap12333, scalarRow12333, sourceIndex, cell12333, BstLean.Part263.envelope, parameters]

theorem repair12333Cell26 :
    0 ≤ cap12333 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12333 (parameters ⟨26,by decide⟩)
      (scalarRow12333.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12333 ⟨26,by decide⟩ ∧
    (scalarRow12333.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12333 ⟨26,by decide⟩ + (scalarRow12333.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12333.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12333.targetFrame := by
  norm_num [cap12333, scalarRow12333, sourceIndex, cell12333, BstLean.Part263.envelope, parameters]

theorem repair12333Cell27 :
    0 ≤ cap12333 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12333 (parameters ⟨27,by decide⟩)
      (scalarRow12333.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12333 ⟨27,by decide⟩ ∧
    (scalarRow12333.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12333 ⟨27,by decide⟩ + (scalarRow12333.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12333.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12333.targetFrame := by
  norm_num [cap12333, scalarRow12333, sourceIndex, cell12333, BstLean.Part263.envelope, parameters]

theorem repair12333Cell28 :
    0 ≤ cap12333 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12333 (parameters ⟨28,by decide⟩)
      (scalarRow12333.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12333 ⟨28,by decide⟩ ∧
    (scalarRow12333.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12333 ⟨28,by decide⟩ + (scalarRow12333.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12333.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12333.targetFrame := by
  norm_num [cap12333, scalarRow12333, sourceIndex, cell12333, BstLean.Part263.envelope, parameters]

theorem repair12333Cell29 :
    0 ≤ cap12333 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12333 (parameters ⟨29,by decide⟩)
      (scalarRow12333.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12333 ⟨29,by decide⟩ ∧
    (scalarRow12333.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12333 ⟨29,by decide⟩ + (scalarRow12333.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12333.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12333.targetFrame := by
  norm_num [cap12333, scalarRow12333, sourceIndex, cell12333, BstLean.Part263.envelope, parameters]

theorem repair12333Cell30 :
    0 ≤ cap12333 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12333 (parameters ⟨30,by decide⟩)
      (scalarRow12333.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12333 ⟨30,by decide⟩ ∧
    (scalarRow12333.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12333 ⟨30,by decide⟩ + (scalarRow12333.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12333.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12333.targetFrame := by
  norm_num [cap12333, scalarRow12333, sourceIndex, cell12333, BstLean.Part263.envelope, parameters]

theorem repair12333Cell31 :
    0 ≤ cap12333 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12333 (parameters ⟨31,by decide⟩)
      (scalarRow12333.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12333 ⟨31,by decide⟩ ∧
    (scalarRow12333.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12333 ⟨31,by decide⟩ + (scalarRow12333.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12333.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12333.targetFrame := by
  norm_num [cap12333, scalarRow12333, sourceIndex, cell12333, BstLean.Part263.envelope, parameters]

theorem repair12333Cell32 :
    0 ≤ cap12333 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12333 (parameters ⟨32,by decide⟩)
      (scalarRow12333.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12333 ⟨32,by decide⟩ ∧
    (scalarRow12333.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12333 ⟨32,by decide⟩ + (scalarRow12333.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12333.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12333.targetFrame := by
  norm_num [cap12333, scalarRow12333, sourceIndex, cell12333, BstLean.Part263.envelope, parameters]

theorem repair12333Cell33 :
    0 ≤ cap12333 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12333 (parameters ⟨33,by decide⟩)
      (scalarRow12333.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12333 ⟨33,by decide⟩ ∧
    (scalarRow12333.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12333 ⟨33,by decide⟩ + (scalarRow12333.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12333.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12333.targetFrame := by
  norm_num [cap12333, scalarRow12333, sourceIndex, cell12333, BstLean.Part263.envelope, parameters]

theorem repair12333Cell34 :
    0 ≤ cap12333 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12333 (parameters ⟨34,by decide⟩)
      (scalarRow12333.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12333 ⟨34,by decide⟩ ∧
    (scalarRow12333.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12333 ⟨34,by decide⟩ + (scalarRow12333.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12333.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12333.targetFrame := by
  norm_num [cap12333, scalarRow12333, sourceIndex, cell12333, BstLean.Part263.envelope, parameters]

theorem repair12333Cell35 :
    0 ≤ cap12333 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12333 (parameters ⟨35,by decide⟩)
      (scalarRow12333.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12333 ⟨35,by decide⟩ ∧
    (scalarRow12333.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12333 ⟨35,by decide⟩ + (scalarRow12333.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12333.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12333.targetFrame := by
  norm_num [cap12333, scalarRow12333, sourceIndex, cell12333, BstLean.Part263.envelope, parameters]

theorem repair12333Cell36 :
    0 ≤ cap12333 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12333 (parameters ⟨36,by decide⟩)
      (scalarRow12333.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12333 ⟨36,by decide⟩ ∧
    (scalarRow12333.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12333 ⟨36,by decide⟩ + (scalarRow12333.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12333.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12333.targetFrame := by
  norm_num [cap12333, scalarRow12333, sourceIndex, cell12333, BstLean.Part263.envelope, parameters]

theorem repair12333Cell37 :
    0 ≤ cap12333 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12333 (parameters ⟨37,by decide⟩)
      (scalarRow12333.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12333 ⟨37,by decide⟩ ∧
    (scalarRow12333.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12333 ⟨37,by decide⟩ + (scalarRow12333.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12333.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12333.targetFrame := by
  norm_num [cap12333, scalarRow12333, sourceIndex, cell12333, BstLean.Part263.envelope, parameters]

theorem repair12333Cell38 :
    0 ≤ cap12333 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12333 (parameters ⟨38,by decide⟩)
      (scalarRow12333.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12333 ⟨38,by decide⟩ ∧
    (scalarRow12333.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12333 ⟨38,by decide⟩ + (scalarRow12333.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12333.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12333.targetFrame := by
  norm_num [cap12333, scalarRow12333, sourceIndex, cell12333, BstLean.Part263.envelope, parameters]

theorem repair12333Cell39 :
    0 ≤ cap12333 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12333 (parameters ⟨39,by decide⟩)
      (scalarRow12333.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12333 ⟨39,by decide⟩ ∧
    (scalarRow12333.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12333 ⟨39,by decide⟩ + (scalarRow12333.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12333.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12333.targetFrame := by
  norm_num [cap12333, scalarRow12333, sourceIndex, cell12333, BstLean.Part263.envelope, parameters]

theorem repair12333Cell40 :
    0 ≤ cap12333 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12333 (parameters ⟨40,by decide⟩)
      (scalarRow12333.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12333 ⟨40,by decide⟩ ∧
    (scalarRow12333.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12333 ⟨40,by decide⟩ + (scalarRow12333.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12333.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12333.targetFrame := by
  norm_num [cap12333, scalarRow12333, sourceIndex, cell12333, BstLean.Part263.envelope, parameters]

theorem repair12333Cell41 :
    0 ≤ cap12333 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12333 (parameters ⟨41,by decide⟩)
      (scalarRow12333.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12333 ⟨41,by decide⟩ ∧
    (scalarRow12333.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12333 ⟨41,by decide⟩ + (scalarRow12333.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12333.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12333.targetFrame := by
  norm_num [cap12333, scalarRow12333, sourceIndex, cell12333, BstLean.Part263.envelope, parameters]

theorem repair12333Cell42 :
    0 ≤ cap12333 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12333 (parameters ⟨42,by decide⟩)
      (scalarRow12333.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12333 ⟨42,by decide⟩ ∧
    (scalarRow12333.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12333 ⟨42,by decide⟩ + (scalarRow12333.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12333.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12333.targetFrame := by
  norm_num [cap12333, scalarRow12333, sourceIndex, cell12333, BstLean.Part263.envelope, parameters]

theorem repair12333Cells (j : Fin 43) :
    0 ≤ cap12333 j ∧
    BstLean.Part263.envelope 12333 (parameters j) (scalarRow12333.table (sourceIndex j)).upper ≤ cap12333 j ∧
    (scalarRow12333.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12333 j + (scalarRow12333.table (sourceIndex j)).centre) /
      (scalarRow12333.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12333.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12333Cell0
  | ⟨1,_⟩ => exact repair12333Cell1
  | ⟨2,_⟩ => exact repair12333Cell2
  | ⟨3,_⟩ => exact repair12333Cell3
  | ⟨4,_⟩ => exact repair12333Cell4
  | ⟨5,_⟩ => exact repair12333Cell5
  | ⟨6,_⟩ => exact repair12333Cell6
  | ⟨7,_⟩ => exact repair12333Cell7
  | ⟨8,_⟩ => exact repair12333Cell8
  | ⟨9,_⟩ => exact repair12333Cell9
  | ⟨10,_⟩ => exact repair12333Cell10
  | ⟨11,_⟩ => exact repair12333Cell11
  | ⟨12,_⟩ => exact repair12333Cell12
  | ⟨13,_⟩ => exact repair12333Cell13
  | ⟨14,_⟩ => exact repair12333Cell14
  | ⟨15,_⟩ => exact repair12333Cell15
  | ⟨16,_⟩ => exact repair12333Cell16
  | ⟨17,_⟩ => exact repair12333Cell17
  | ⟨18,_⟩ => exact repair12333Cell18
  | ⟨19,_⟩ => exact repair12333Cell19
  | ⟨20,_⟩ => exact repair12333Cell20
  | ⟨21,_⟩ => exact repair12333Cell21
  | ⟨22,_⟩ => exact repair12333Cell22
  | ⟨23,_⟩ => exact repair12333Cell23
  | ⟨24,_⟩ => exact repair12333Cell24
  | ⟨25,_⟩ => exact repair12333Cell25
  | ⟨26,_⟩ => exact repair12333Cell26
  | ⟨27,_⟩ => exact repair12333Cell27
  | ⟨28,_⟩ => exact repair12333Cell28
  | ⟨29,_⟩ => exact repair12333Cell29
  | ⟨30,_⟩ => exact repair12333Cell30
  | ⟨31,_⟩ => exact repair12333Cell31
  | ⟨32,_⟩ => exact repair12333Cell32
  | ⟨33,_⟩ => exact repair12333Cell33
  | ⟨34,_⟩ => exact repair12333Cell34
  | ⟨35,_⟩ => exact repair12333Cell35
  | ⟨36,_⟩ => exact repair12333Cell36
  | ⟨37,_⟩ => exact repair12333Cell37
  | ⟨38,_⟩ => exact repair12333Cell38
  | ⟨39,_⟩ => exact repair12333Cell39
  | ⟨40,_⟩ => exact repair12333Cell40
  | ⟨41,_⟩ => exact repair12333Cell41
  | ⟨42,_⟩ => exact repair12333Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12333 : FrameRepair 12333 scalarRow12333 where
  cap := cap12333
  cap_nonneg := fun j => (repair12333Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12333])
  endpoint := fun j => (repair12333Cells j).2.1
  endpoint_upper := fun j => (repair12333Cells j).2.2.1
  frame := fun j => (repair12333Cells j).2.2.2

noncomputable def cap12334 : Fin 43 → ℝ
  | ⟨0,_⟩ => (275944501 / 1000000000 : ℝ)
  | ⟨1,_⟩ => (276347067 / 1000000000 : ℝ)
  | ⟨2,_⟩ => (276748639 / 1000000000 : ℝ)
  | ⟨3,_⟩ => (277149213 / 1000000000 : ℝ)
  | ⟨4,_⟩ => (138774399 / 500000000 : ℝ)
  | ⟨5,_⟩ => (138973697 / 500000000 : ℝ)
  | ⟨6,_⟩ => (278344529 / 1000000000 : ℝ)
  | ⟨7,_⟩ => (278741159 / 1000000000 : ℝ)
  | ⟨8,_⟩ => (139568407 / 500000000 : ℝ)
  | ⟨9,_⟩ => (279531497 / 1000000000 : ℝ)
  | ⟨10,_⟩ => (27992521 / 100000000 : ℝ)
  | ⟨11,_⟩ => (11212699 / 40000000 : ℝ)
  | ⟨12,_⟩ => (140354631 / 500000000 : ℝ)
  | ⟨13,_⟩ => (70274901 / 250000000 : ℝ)
  | ⟨14,_⟩ => (281489879 / 1000000000 : ℝ)
  | ⟨15,_⟩ => (140939527 / 500000000 : ℝ)
  | ⟨16,_⟩ => (35283411 / 125000000 : ℝ)
  | ⟨17,_⟩ => (282654591 / 1000000000 : ℝ)
  | ⟨18,_⟩ => (56608191 / 200000000 : ℝ)
  | ⟨19,_⟩ => (283426391 / 1000000000 : ℝ)
  | ⟨20,_⟩ => (2838109 / 10000000 : ℝ)
  | ⟨21,_⟩ => (142097247 / 500000000 : ℝ)
  | ⟨22,_⟩ => (71144291 / 250000000 : ℝ)
  | ⟨23,_⟩ => (35619803 / 125000000 : ℝ)
  | ⟨24,_⟩ => (35667409 / 125000000 : ℝ)
  | ⟨25,_⟩ => (7142969 / 25000000 : ℝ)
  | ⟨26,_⟩ => (286097843 / 1000000000 : ℝ)
  | ⟨27,_⟩ => (35809441 / 125000000 : ℝ)
  | ⟨28,_⟩ => (286852317 / 1000000000 : ℝ)
  | ⟨29,_⟩ => (287228211 / 1000000000 : ℝ)
  | ⟨30,_⟩ => (287602711 / 1000000000 : ℝ)
  | ⟨31,_⟩ => (71994207 / 250000000 : ℝ)
  | ⟨32,_⟩ => (57670013 / 200000000 : ℝ)
  | ⟨33,_⟩ => (288721911 / 1000000000 : ℝ)
  | ⟨34,_⟩ => (72273221 / 250000000 : ℝ)
  | ⟨35,_⟩ => (57892597 / 200000000 : ℝ)
  | ⟨36,_⟩ => (28983221 / 100000000 : ℝ)
  | ⟨37,_⟩ => (566798 / 1953125 : ℝ)
  | ⟨38,_⟩ => (290568077 / 1000000000 : ℝ)
  | ⟨39,_⟩ => (290934207 / 1000000000 : ℝ)
  | ⟨40,_⟩ => (145649739 / 500000000 : ℝ)
  | ⟨41,_⟩ => (291663899 / 1000000000 : ℝ)
  | ⟨42,_⟩ => (73006867 / 250000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12334Cell0 :
    0 ≤ cap12334 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12334 (parameters ⟨0,by decide⟩)
      (scalarRow12334.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12334 ⟨0,by decide⟩ ∧
    (scalarRow12334.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12334 ⟨0,by decide⟩ + (scalarRow12334.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12334.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12334.targetFrame := by
  norm_num [cap12334, scalarRow12334, sourceIndex, cell12334, BstLean.Part263.envelope, parameters]

theorem repair12334Cell1 :
    0 ≤ cap12334 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12334 (parameters ⟨1,by decide⟩)
      (scalarRow12334.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12334 ⟨1,by decide⟩ ∧
    (scalarRow12334.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12334 ⟨1,by decide⟩ + (scalarRow12334.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12334.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12334.targetFrame := by
  norm_num [cap12334, scalarRow12334, sourceIndex, cell12334, BstLean.Part263.envelope, parameters]

theorem repair12334Cell2 :
    0 ≤ cap12334 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12334 (parameters ⟨2,by decide⟩)
      (scalarRow12334.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12334 ⟨2,by decide⟩ ∧
    (scalarRow12334.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12334 ⟨2,by decide⟩ + (scalarRow12334.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12334.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12334.targetFrame := by
  norm_num [cap12334, scalarRow12334, sourceIndex, cell12334, BstLean.Part263.envelope, parameters]

theorem repair12334Cell3 :
    0 ≤ cap12334 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12334 (parameters ⟨3,by decide⟩)
      (scalarRow12334.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12334 ⟨3,by decide⟩ ∧
    (scalarRow12334.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12334 ⟨3,by decide⟩ + (scalarRow12334.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12334.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12334.targetFrame := by
  norm_num [cap12334, scalarRow12334, sourceIndex, cell12334, BstLean.Part263.envelope, parameters]

theorem repair12334Cell4 :
    0 ≤ cap12334 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12334 (parameters ⟨4,by decide⟩)
      (scalarRow12334.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12334 ⟨4,by decide⟩ ∧
    (scalarRow12334.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12334 ⟨4,by decide⟩ + (scalarRow12334.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12334.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12334.targetFrame := by
  norm_num [cap12334, scalarRow12334, sourceIndex, cell12334, BstLean.Part263.envelope, parameters]

theorem repair12334Cell5 :
    0 ≤ cap12334 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12334 (parameters ⟨5,by decide⟩)
      (scalarRow12334.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12334 ⟨5,by decide⟩ ∧
    (scalarRow12334.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12334 ⟨5,by decide⟩ + (scalarRow12334.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12334.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12334.targetFrame := by
  norm_num [cap12334, scalarRow12334, sourceIndex, cell12334, BstLean.Part263.envelope, parameters]

theorem repair12334Cell6 :
    0 ≤ cap12334 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12334 (parameters ⟨6,by decide⟩)
      (scalarRow12334.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12334 ⟨6,by decide⟩ ∧
    (scalarRow12334.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12334 ⟨6,by decide⟩ + (scalarRow12334.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12334.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12334.targetFrame := by
  norm_num [cap12334, scalarRow12334, sourceIndex, cell12334, BstLean.Part263.envelope, parameters]

theorem repair12334Cell7 :
    0 ≤ cap12334 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12334 (parameters ⟨7,by decide⟩)
      (scalarRow12334.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12334 ⟨7,by decide⟩ ∧
    (scalarRow12334.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12334 ⟨7,by decide⟩ + (scalarRow12334.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12334.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12334.targetFrame := by
  norm_num [cap12334, scalarRow12334, sourceIndex, cell12334, BstLean.Part263.envelope, parameters]

theorem repair12334Cell8 :
    0 ≤ cap12334 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12334 (parameters ⟨8,by decide⟩)
      (scalarRow12334.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12334 ⟨8,by decide⟩ ∧
    (scalarRow12334.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12334 ⟨8,by decide⟩ + (scalarRow12334.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12334.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12334.targetFrame := by
  norm_num [cap12334, scalarRow12334, sourceIndex, cell12334, BstLean.Part263.envelope, parameters]

theorem repair12334Cell9 :
    0 ≤ cap12334 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12334 (parameters ⟨9,by decide⟩)
      (scalarRow12334.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12334 ⟨9,by decide⟩ ∧
    (scalarRow12334.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12334 ⟨9,by decide⟩ + (scalarRow12334.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12334.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12334.targetFrame := by
  norm_num [cap12334, scalarRow12334, sourceIndex, cell12334, BstLean.Part263.envelope, parameters]

theorem repair12334Cell10 :
    0 ≤ cap12334 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12334 (parameters ⟨10,by decide⟩)
      (scalarRow12334.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12334 ⟨10,by decide⟩ ∧
    (scalarRow12334.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12334 ⟨10,by decide⟩ + (scalarRow12334.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12334.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12334.targetFrame := by
  norm_num [cap12334, scalarRow12334, sourceIndex, cell12334, BstLean.Part263.envelope, parameters]

theorem repair12334Cell11 :
    0 ≤ cap12334 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12334 (parameters ⟨11,by decide⟩)
      (scalarRow12334.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12334 ⟨11,by decide⟩ ∧
    (scalarRow12334.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12334 ⟨11,by decide⟩ + (scalarRow12334.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12334.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12334.targetFrame := by
  norm_num [cap12334, scalarRow12334, sourceIndex, cell12334, BstLean.Part263.envelope, parameters]

theorem repair12334Cell12 :
    0 ≤ cap12334 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12334 (parameters ⟨12,by decide⟩)
      (scalarRow12334.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12334 ⟨12,by decide⟩ ∧
    (scalarRow12334.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12334 ⟨12,by decide⟩ + (scalarRow12334.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12334.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12334.targetFrame := by
  norm_num [cap12334, scalarRow12334, sourceIndex, cell12334, BstLean.Part263.envelope, parameters]

theorem repair12334Cell13 :
    0 ≤ cap12334 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12334 (parameters ⟨13,by decide⟩)
      (scalarRow12334.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12334 ⟨13,by decide⟩ ∧
    (scalarRow12334.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12334 ⟨13,by decide⟩ + (scalarRow12334.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12334.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12334.targetFrame := by
  norm_num [cap12334, scalarRow12334, sourceIndex, cell12334, BstLean.Part263.envelope, parameters]

theorem repair12334Cell14 :
    0 ≤ cap12334 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12334 (parameters ⟨14,by decide⟩)
      (scalarRow12334.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12334 ⟨14,by decide⟩ ∧
    (scalarRow12334.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12334 ⟨14,by decide⟩ + (scalarRow12334.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12334.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12334.targetFrame := by
  norm_num [cap12334, scalarRow12334, sourceIndex, cell12334, BstLean.Part263.envelope, parameters]

theorem repair12334Cell15 :
    0 ≤ cap12334 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12334 (parameters ⟨15,by decide⟩)
      (scalarRow12334.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12334 ⟨15,by decide⟩ ∧
    (scalarRow12334.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12334 ⟨15,by decide⟩ + (scalarRow12334.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12334.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12334.targetFrame := by
  norm_num [cap12334, scalarRow12334, sourceIndex, cell12334, BstLean.Part263.envelope, parameters]

theorem repair12334Cell16 :
    0 ≤ cap12334 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12334 (parameters ⟨16,by decide⟩)
      (scalarRow12334.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12334 ⟨16,by decide⟩ ∧
    (scalarRow12334.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12334 ⟨16,by decide⟩ + (scalarRow12334.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12334.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12334.targetFrame := by
  norm_num [cap12334, scalarRow12334, sourceIndex, cell12334, BstLean.Part263.envelope, parameters]

theorem repair12334Cell17 :
    0 ≤ cap12334 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12334 (parameters ⟨17,by decide⟩)
      (scalarRow12334.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12334 ⟨17,by decide⟩ ∧
    (scalarRow12334.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12334 ⟨17,by decide⟩ + (scalarRow12334.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12334.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12334.targetFrame := by
  norm_num [cap12334, scalarRow12334, sourceIndex, cell12334, BstLean.Part263.envelope, parameters]

theorem repair12334Cell18 :
    0 ≤ cap12334 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12334 (parameters ⟨18,by decide⟩)
      (scalarRow12334.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12334 ⟨18,by decide⟩ ∧
    (scalarRow12334.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12334 ⟨18,by decide⟩ + (scalarRow12334.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12334.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12334.targetFrame := by
  norm_num [cap12334, scalarRow12334, sourceIndex, cell12334, BstLean.Part263.envelope, parameters]

theorem repair12334Cell19 :
    0 ≤ cap12334 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12334 (parameters ⟨19,by decide⟩)
      (scalarRow12334.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12334 ⟨19,by decide⟩ ∧
    (scalarRow12334.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12334 ⟨19,by decide⟩ + (scalarRow12334.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12334.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12334.targetFrame := by
  norm_num [cap12334, scalarRow12334, sourceIndex, cell12334, BstLean.Part263.envelope, parameters]

theorem repair12334Cell20 :
    0 ≤ cap12334 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12334 (parameters ⟨20,by decide⟩)
      (scalarRow12334.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12334 ⟨20,by decide⟩ ∧
    (scalarRow12334.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12334 ⟨20,by decide⟩ + (scalarRow12334.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12334.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12334.targetFrame := by
  norm_num [cap12334, scalarRow12334, sourceIndex, cell12334, BstLean.Part263.envelope, parameters]

theorem repair12334Cell21 :
    0 ≤ cap12334 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12334 (parameters ⟨21,by decide⟩)
      (scalarRow12334.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12334 ⟨21,by decide⟩ ∧
    (scalarRow12334.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12334 ⟨21,by decide⟩ + (scalarRow12334.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12334.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12334.targetFrame := by
  norm_num [cap12334, scalarRow12334, sourceIndex, cell12334, BstLean.Part263.envelope, parameters]

theorem repair12334Cell22 :
    0 ≤ cap12334 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12334 (parameters ⟨22,by decide⟩)
      (scalarRow12334.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12334 ⟨22,by decide⟩ ∧
    (scalarRow12334.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12334 ⟨22,by decide⟩ + (scalarRow12334.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12334.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12334.targetFrame := by
  norm_num [cap12334, scalarRow12334, sourceIndex, cell12334, BstLean.Part263.envelope, parameters]

theorem repair12334Cell23 :
    0 ≤ cap12334 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12334 (parameters ⟨23,by decide⟩)
      (scalarRow12334.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12334 ⟨23,by decide⟩ ∧
    (scalarRow12334.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12334 ⟨23,by decide⟩ + (scalarRow12334.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12334.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12334.targetFrame := by
  norm_num [cap12334, scalarRow12334, sourceIndex, cell12334, BstLean.Part263.envelope, parameters]

theorem repair12334Cell24 :
    0 ≤ cap12334 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12334 (parameters ⟨24,by decide⟩)
      (scalarRow12334.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12334 ⟨24,by decide⟩ ∧
    (scalarRow12334.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12334 ⟨24,by decide⟩ + (scalarRow12334.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12334.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12334.targetFrame := by
  norm_num [cap12334, scalarRow12334, sourceIndex, cell12334, BstLean.Part263.envelope, parameters]

theorem repair12334Cell25 :
    0 ≤ cap12334 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12334 (parameters ⟨25,by decide⟩)
      (scalarRow12334.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12334 ⟨25,by decide⟩ ∧
    (scalarRow12334.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12334 ⟨25,by decide⟩ + (scalarRow12334.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12334.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12334.targetFrame := by
  norm_num [cap12334, scalarRow12334, sourceIndex, cell12334, BstLean.Part263.envelope, parameters]

theorem repair12334Cell26 :
    0 ≤ cap12334 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12334 (parameters ⟨26,by decide⟩)
      (scalarRow12334.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12334 ⟨26,by decide⟩ ∧
    (scalarRow12334.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12334 ⟨26,by decide⟩ + (scalarRow12334.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12334.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12334.targetFrame := by
  norm_num [cap12334, scalarRow12334, sourceIndex, cell12334, BstLean.Part263.envelope, parameters]

theorem repair12334Cell27 :
    0 ≤ cap12334 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12334 (parameters ⟨27,by decide⟩)
      (scalarRow12334.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12334 ⟨27,by decide⟩ ∧
    (scalarRow12334.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12334 ⟨27,by decide⟩ + (scalarRow12334.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12334.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12334.targetFrame := by
  norm_num [cap12334, scalarRow12334, sourceIndex, cell12334, BstLean.Part263.envelope, parameters]

theorem repair12334Cell28 :
    0 ≤ cap12334 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12334 (parameters ⟨28,by decide⟩)
      (scalarRow12334.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12334 ⟨28,by decide⟩ ∧
    (scalarRow12334.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12334 ⟨28,by decide⟩ + (scalarRow12334.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12334.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12334.targetFrame := by
  norm_num [cap12334, scalarRow12334, sourceIndex, cell12334, BstLean.Part263.envelope, parameters]

theorem repair12334Cell29 :
    0 ≤ cap12334 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12334 (parameters ⟨29,by decide⟩)
      (scalarRow12334.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12334 ⟨29,by decide⟩ ∧
    (scalarRow12334.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12334 ⟨29,by decide⟩ + (scalarRow12334.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12334.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12334.targetFrame := by
  norm_num [cap12334, scalarRow12334, sourceIndex, cell12334, BstLean.Part263.envelope, parameters]

theorem repair12334Cell30 :
    0 ≤ cap12334 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12334 (parameters ⟨30,by decide⟩)
      (scalarRow12334.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12334 ⟨30,by decide⟩ ∧
    (scalarRow12334.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12334 ⟨30,by decide⟩ + (scalarRow12334.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12334.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12334.targetFrame := by
  norm_num [cap12334, scalarRow12334, sourceIndex, cell12334, BstLean.Part263.envelope, parameters]

theorem repair12334Cell31 :
    0 ≤ cap12334 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12334 (parameters ⟨31,by decide⟩)
      (scalarRow12334.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12334 ⟨31,by decide⟩ ∧
    (scalarRow12334.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12334 ⟨31,by decide⟩ + (scalarRow12334.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12334.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12334.targetFrame := by
  norm_num [cap12334, scalarRow12334, sourceIndex, cell12334, BstLean.Part263.envelope, parameters]

theorem repair12334Cell32 :
    0 ≤ cap12334 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12334 (parameters ⟨32,by decide⟩)
      (scalarRow12334.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12334 ⟨32,by decide⟩ ∧
    (scalarRow12334.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12334 ⟨32,by decide⟩ + (scalarRow12334.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12334.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12334.targetFrame := by
  norm_num [cap12334, scalarRow12334, sourceIndex, cell12334, BstLean.Part263.envelope, parameters]

theorem repair12334Cell33 :
    0 ≤ cap12334 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12334 (parameters ⟨33,by decide⟩)
      (scalarRow12334.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12334 ⟨33,by decide⟩ ∧
    (scalarRow12334.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12334 ⟨33,by decide⟩ + (scalarRow12334.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12334.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12334.targetFrame := by
  norm_num [cap12334, scalarRow12334, sourceIndex, cell12334, BstLean.Part263.envelope, parameters]

theorem repair12334Cell34 :
    0 ≤ cap12334 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12334 (parameters ⟨34,by decide⟩)
      (scalarRow12334.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12334 ⟨34,by decide⟩ ∧
    (scalarRow12334.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12334 ⟨34,by decide⟩ + (scalarRow12334.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12334.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12334.targetFrame := by
  norm_num [cap12334, scalarRow12334, sourceIndex, cell12334, BstLean.Part263.envelope, parameters]

theorem repair12334Cell35 :
    0 ≤ cap12334 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12334 (parameters ⟨35,by decide⟩)
      (scalarRow12334.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12334 ⟨35,by decide⟩ ∧
    (scalarRow12334.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12334 ⟨35,by decide⟩ + (scalarRow12334.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12334.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12334.targetFrame := by
  norm_num [cap12334, scalarRow12334, sourceIndex, cell12334, BstLean.Part263.envelope, parameters]

theorem repair12334Cell36 :
    0 ≤ cap12334 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12334 (parameters ⟨36,by decide⟩)
      (scalarRow12334.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12334 ⟨36,by decide⟩ ∧
    (scalarRow12334.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12334 ⟨36,by decide⟩ + (scalarRow12334.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12334.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12334.targetFrame := by
  norm_num [cap12334, scalarRow12334, sourceIndex, cell12334, BstLean.Part263.envelope, parameters]

theorem repair12334Cell37 :
    0 ≤ cap12334 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12334 (parameters ⟨37,by decide⟩)
      (scalarRow12334.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12334 ⟨37,by decide⟩ ∧
    (scalarRow12334.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12334 ⟨37,by decide⟩ + (scalarRow12334.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12334.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12334.targetFrame := by
  norm_num [cap12334, scalarRow12334, sourceIndex, cell12334, BstLean.Part263.envelope, parameters]

theorem repair12334Cell38 :
    0 ≤ cap12334 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12334 (parameters ⟨38,by decide⟩)
      (scalarRow12334.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12334 ⟨38,by decide⟩ ∧
    (scalarRow12334.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12334 ⟨38,by decide⟩ + (scalarRow12334.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12334.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12334.targetFrame := by
  norm_num [cap12334, scalarRow12334, sourceIndex, cell12334, BstLean.Part263.envelope, parameters]

theorem repair12334Cell39 :
    0 ≤ cap12334 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12334 (parameters ⟨39,by decide⟩)
      (scalarRow12334.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12334 ⟨39,by decide⟩ ∧
    (scalarRow12334.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12334 ⟨39,by decide⟩ + (scalarRow12334.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12334.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12334.targetFrame := by
  norm_num [cap12334, scalarRow12334, sourceIndex, cell12334, BstLean.Part263.envelope, parameters]

theorem repair12334Cell40 :
    0 ≤ cap12334 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12334 (parameters ⟨40,by decide⟩)
      (scalarRow12334.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12334 ⟨40,by decide⟩ ∧
    (scalarRow12334.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12334 ⟨40,by decide⟩ + (scalarRow12334.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12334.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12334.targetFrame := by
  norm_num [cap12334, scalarRow12334, sourceIndex, cell12334, BstLean.Part263.envelope, parameters]

theorem repair12334Cell41 :
    0 ≤ cap12334 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12334 (parameters ⟨41,by decide⟩)
      (scalarRow12334.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12334 ⟨41,by decide⟩ ∧
    (scalarRow12334.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12334 ⟨41,by decide⟩ + (scalarRow12334.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12334.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12334.targetFrame := by
  norm_num [cap12334, scalarRow12334, sourceIndex, cell12334, BstLean.Part263.envelope, parameters]

theorem repair12334Cell42 :
    0 ≤ cap12334 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12334 (parameters ⟨42,by decide⟩)
      (scalarRow12334.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12334 ⟨42,by decide⟩ ∧
    (scalarRow12334.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12334 ⟨42,by decide⟩ + (scalarRow12334.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12334.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12334.targetFrame := by
  norm_num [cap12334, scalarRow12334, sourceIndex, cell12334, BstLean.Part263.envelope, parameters]

theorem repair12334Cells (j : Fin 43) :
    0 ≤ cap12334 j ∧
    BstLean.Part263.envelope 12334 (parameters j) (scalarRow12334.table (sourceIndex j)).upper ≤ cap12334 j ∧
    (scalarRow12334.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12334 j + (scalarRow12334.table (sourceIndex j)).centre) /
      (scalarRow12334.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12334.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12334Cell0
  | ⟨1,_⟩ => exact repair12334Cell1
  | ⟨2,_⟩ => exact repair12334Cell2
  | ⟨3,_⟩ => exact repair12334Cell3
  | ⟨4,_⟩ => exact repair12334Cell4
  | ⟨5,_⟩ => exact repair12334Cell5
  | ⟨6,_⟩ => exact repair12334Cell6
  | ⟨7,_⟩ => exact repair12334Cell7
  | ⟨8,_⟩ => exact repair12334Cell8
  | ⟨9,_⟩ => exact repair12334Cell9
  | ⟨10,_⟩ => exact repair12334Cell10
  | ⟨11,_⟩ => exact repair12334Cell11
  | ⟨12,_⟩ => exact repair12334Cell12
  | ⟨13,_⟩ => exact repair12334Cell13
  | ⟨14,_⟩ => exact repair12334Cell14
  | ⟨15,_⟩ => exact repair12334Cell15
  | ⟨16,_⟩ => exact repair12334Cell16
  | ⟨17,_⟩ => exact repair12334Cell17
  | ⟨18,_⟩ => exact repair12334Cell18
  | ⟨19,_⟩ => exact repair12334Cell19
  | ⟨20,_⟩ => exact repair12334Cell20
  | ⟨21,_⟩ => exact repair12334Cell21
  | ⟨22,_⟩ => exact repair12334Cell22
  | ⟨23,_⟩ => exact repair12334Cell23
  | ⟨24,_⟩ => exact repair12334Cell24
  | ⟨25,_⟩ => exact repair12334Cell25
  | ⟨26,_⟩ => exact repair12334Cell26
  | ⟨27,_⟩ => exact repair12334Cell27
  | ⟨28,_⟩ => exact repair12334Cell28
  | ⟨29,_⟩ => exact repair12334Cell29
  | ⟨30,_⟩ => exact repair12334Cell30
  | ⟨31,_⟩ => exact repair12334Cell31
  | ⟨32,_⟩ => exact repair12334Cell32
  | ⟨33,_⟩ => exact repair12334Cell33
  | ⟨34,_⟩ => exact repair12334Cell34
  | ⟨35,_⟩ => exact repair12334Cell35
  | ⟨36,_⟩ => exact repair12334Cell36
  | ⟨37,_⟩ => exact repair12334Cell37
  | ⟨38,_⟩ => exact repair12334Cell38
  | ⟨39,_⟩ => exact repair12334Cell39
  | ⟨40,_⟩ => exact repair12334Cell40
  | ⟨41,_⟩ => exact repair12334Cell41
  | ⟨42,_⟩ => exact repair12334Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12334 : FrameRepair 12334 scalarRow12334 where
  cap := cap12334
  cap_nonneg := fun j => (repair12334Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12334])
  endpoint := fun j => (repair12334Cells j).2.1
  endpoint_upper := fun j => (repair12334Cells j).2.2.1
  frame := fun j => (repair12334Cells j).2.2.2

noncomputable def cap12335 : Fin 43 → ℝ
  | ⟨0,_⟩ => (137972213 / 500000000 : ℝ)
  | ⟨1,_⟩ => (55269397 / 200000000 : ℝ)
  | ⟨2,_⟩ => (276748551 / 1000000000 : ℝ)
  | ⟨3,_⟩ => (277149119 / 1000000000 : ℝ)
  | ⟨4,_⟩ => (138774349 / 500000000 : ℝ)
  | ⟨5,_⟩ => (277947287 / 1000000000 : ℝ)
  | ⟨6,_⟩ => (8698263 / 31250000 : ℝ)
  | ⟨7,_⟩ => (3484263 / 12500000 : ℝ)
  | ⟨8,_⟩ => (17446043 / 62500000 : ℝ)
  | ⟨9,_⟩ => (55906273 / 200000000 : ℝ)
  | ⟨10,_⟩ => (279925071 / 1000000000 : ℝ)
  | ⟨11,_⟩ => (280317329 / 1000000000 : ℝ)
  | ⟨12,_⟩ => (280709111 / 1000000000 : ℝ)
  | ⟨13,_⟩ => (140549723 / 500000000 : ℝ)
  | ⟨14,_⟩ => (56297943 / 200000000 : ℝ)
  | ⟨15,_⟩ => (70469721 / 250000000 : ℝ)
  | ⟨16,_⟩ => (282267111 / 1000000000 : ℝ)
  | ⟨17,_⟩ => (35331801 / 125000000 : ℝ)
  | ⟨18,_⟩ => (141520383 / 500000000 : ℝ)
  | ⟨19,_⟩ => (70856549 / 250000000 : ℝ)
  | ⟨20,_⟩ => (283810699 / 1000000000 : ℝ)
  | ⟨21,_⟩ => (284194287 / 1000000000 : ℝ)
  | ⟨22,_⟩ => (284576951 / 1000000000 : ℝ)
  | ⟨23,_⟩ => (56991641 / 200000000 : ℝ)
  | ⟨24,_⟩ => (285339047 / 1000000000 : ℝ)
  | ⟨25,_⟩ => (558044 / 1953125 : ℝ)
  | ⟨26,_⟩ => (57219521 / 200000000 : ℝ)
  | ⟨27,_⟩ => (71618821 / 250000000 : ℝ)
  | ⟨28,_⟩ => (286852067 / 1000000000 : ℝ)
  | ⟨29,_⟩ => (143613977 / 500000000 : ℝ)
  | ⟨30,_⟩ => (287602449 / 1000000000 : ℝ)
  | ⟨31,_⟩ => (3599707 / 12500000 : ℝ)
  | ⟨32,_⟩ => (28834979 / 100000000 : ℝ)
  | ⟨33,_⟩ => (288721631 / 1000000000 : ℝ)
  | ⟨34,_⟩ => (289092597 / 1000000000 : ℝ)
  | ⟨35,_⟩ => (72365673 / 250000000 : ℝ)
  | ⟨36,_⟩ => (289831911 / 1000000000 : ℝ)
  | ⟨37,_⟩ => (290200271 / 1000000000 : ℝ)
  | ⟨38,_⟩ => (290567767 / 1000000000 : ℝ)
  | ⟨39,_⟩ => (290933891 / 1000000000 : ℝ)
  | ⟨40,_⟩ => (72824789 / 250000000 : ℝ)
  | ⟨41,_⟩ => (291663571 / 1000000000 : ℝ)
  | ⟨42,_⟩ => (146013567 / 500000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12335Cell0 :
    0 ≤ cap12335 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12335 (parameters ⟨0,by decide⟩)
      (scalarRow12335.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12335 ⟨0,by decide⟩ ∧
    (scalarRow12335.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12335 ⟨0,by decide⟩ + (scalarRow12335.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12335.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12335.targetFrame := by
  norm_num [cap12335, scalarRow12335, sourceIndex, cell12335, BstLean.Part263.envelope, parameters]

theorem repair12335Cell1 :
    0 ≤ cap12335 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12335 (parameters ⟨1,by decide⟩)
      (scalarRow12335.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12335 ⟨1,by decide⟩ ∧
    (scalarRow12335.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12335 ⟨1,by decide⟩ + (scalarRow12335.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12335.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12335.targetFrame := by
  norm_num [cap12335, scalarRow12335, sourceIndex, cell12335, BstLean.Part263.envelope, parameters]

theorem repair12335Cell2 :
    0 ≤ cap12335 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12335 (parameters ⟨2,by decide⟩)
      (scalarRow12335.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12335 ⟨2,by decide⟩ ∧
    (scalarRow12335.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12335 ⟨2,by decide⟩ + (scalarRow12335.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12335.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12335.targetFrame := by
  norm_num [cap12335, scalarRow12335, sourceIndex, cell12335, BstLean.Part263.envelope, parameters]

theorem repair12335Cell3 :
    0 ≤ cap12335 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12335 (parameters ⟨3,by decide⟩)
      (scalarRow12335.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12335 ⟨3,by decide⟩ ∧
    (scalarRow12335.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12335 ⟨3,by decide⟩ + (scalarRow12335.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12335.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12335.targetFrame := by
  norm_num [cap12335, scalarRow12335, sourceIndex, cell12335, BstLean.Part263.envelope, parameters]

theorem repair12335Cell4 :
    0 ≤ cap12335 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12335 (parameters ⟨4,by decide⟩)
      (scalarRow12335.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12335 ⟨4,by decide⟩ ∧
    (scalarRow12335.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12335 ⟨4,by decide⟩ + (scalarRow12335.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12335.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12335.targetFrame := by
  norm_num [cap12335, scalarRow12335, sourceIndex, cell12335, BstLean.Part263.envelope, parameters]

theorem repair12335Cell5 :
    0 ≤ cap12335 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12335 (parameters ⟨5,by decide⟩)
      (scalarRow12335.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12335 ⟨5,by decide⟩ ∧
    (scalarRow12335.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12335 ⟨5,by decide⟩ + (scalarRow12335.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12335.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12335.targetFrame := by
  norm_num [cap12335, scalarRow12335, sourceIndex, cell12335, BstLean.Part263.envelope, parameters]

theorem repair12335Cell6 :
    0 ≤ cap12335 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12335 (parameters ⟨6,by decide⟩)
      (scalarRow12335.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12335 ⟨6,by decide⟩ ∧
    (scalarRow12335.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12335 ⟨6,by decide⟩ + (scalarRow12335.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12335.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12335.targetFrame := by
  norm_num [cap12335, scalarRow12335, sourceIndex, cell12335, BstLean.Part263.envelope, parameters]

theorem repair12335Cell7 :
    0 ≤ cap12335 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12335 (parameters ⟨7,by decide⟩)
      (scalarRow12335.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12335 ⟨7,by decide⟩ ∧
    (scalarRow12335.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12335 ⟨7,by decide⟩ + (scalarRow12335.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12335.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12335.targetFrame := by
  norm_num [cap12335, scalarRow12335, sourceIndex, cell12335, BstLean.Part263.envelope, parameters]

theorem repair12335Cell8 :
    0 ≤ cap12335 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12335 (parameters ⟨8,by decide⟩)
      (scalarRow12335.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12335 ⟨8,by decide⟩ ∧
    (scalarRow12335.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12335 ⟨8,by decide⟩ + (scalarRow12335.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12335.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12335.targetFrame := by
  norm_num [cap12335, scalarRow12335, sourceIndex, cell12335, BstLean.Part263.envelope, parameters]

theorem repair12335Cell9 :
    0 ≤ cap12335 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12335 (parameters ⟨9,by decide⟩)
      (scalarRow12335.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12335 ⟨9,by decide⟩ ∧
    (scalarRow12335.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12335 ⟨9,by decide⟩ + (scalarRow12335.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12335.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12335.targetFrame := by
  norm_num [cap12335, scalarRow12335, sourceIndex, cell12335, BstLean.Part263.envelope, parameters]

theorem repair12335Cell10 :
    0 ≤ cap12335 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12335 (parameters ⟨10,by decide⟩)
      (scalarRow12335.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12335 ⟨10,by decide⟩ ∧
    (scalarRow12335.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12335 ⟨10,by decide⟩ + (scalarRow12335.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12335.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12335.targetFrame := by
  norm_num [cap12335, scalarRow12335, sourceIndex, cell12335, BstLean.Part263.envelope, parameters]

theorem repair12335Cell11 :
    0 ≤ cap12335 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12335 (parameters ⟨11,by decide⟩)
      (scalarRow12335.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12335 ⟨11,by decide⟩ ∧
    (scalarRow12335.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12335 ⟨11,by decide⟩ + (scalarRow12335.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12335.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12335.targetFrame := by
  norm_num [cap12335, scalarRow12335, sourceIndex, cell12335, BstLean.Part263.envelope, parameters]

theorem repair12335Cell12 :
    0 ≤ cap12335 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12335 (parameters ⟨12,by decide⟩)
      (scalarRow12335.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12335 ⟨12,by decide⟩ ∧
    (scalarRow12335.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12335 ⟨12,by decide⟩ + (scalarRow12335.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12335.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12335.targetFrame := by
  norm_num [cap12335, scalarRow12335, sourceIndex, cell12335, BstLean.Part263.envelope, parameters]

theorem repair12335Cell13 :
    0 ≤ cap12335 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12335 (parameters ⟨13,by decide⟩)
      (scalarRow12335.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12335 ⟨13,by decide⟩ ∧
    (scalarRow12335.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12335 ⟨13,by decide⟩ + (scalarRow12335.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12335.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12335.targetFrame := by
  norm_num [cap12335, scalarRow12335, sourceIndex, cell12335, BstLean.Part263.envelope, parameters]

theorem repair12335Cell14 :
    0 ≤ cap12335 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12335 (parameters ⟨14,by decide⟩)
      (scalarRow12335.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12335 ⟨14,by decide⟩ ∧
    (scalarRow12335.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12335 ⟨14,by decide⟩ + (scalarRow12335.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12335.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12335.targetFrame := by
  norm_num [cap12335, scalarRow12335, sourceIndex, cell12335, BstLean.Part263.envelope, parameters]

theorem repair12335Cell15 :
    0 ≤ cap12335 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12335 (parameters ⟨15,by decide⟩)
      (scalarRow12335.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12335 ⟨15,by decide⟩ ∧
    (scalarRow12335.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12335 ⟨15,by decide⟩ + (scalarRow12335.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12335.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12335.targetFrame := by
  norm_num [cap12335, scalarRow12335, sourceIndex, cell12335, BstLean.Part263.envelope, parameters]

theorem repair12335Cell16 :
    0 ≤ cap12335 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12335 (parameters ⟨16,by decide⟩)
      (scalarRow12335.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12335 ⟨16,by decide⟩ ∧
    (scalarRow12335.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12335 ⟨16,by decide⟩ + (scalarRow12335.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12335.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12335.targetFrame := by
  norm_num [cap12335, scalarRow12335, sourceIndex, cell12335, BstLean.Part263.envelope, parameters]

theorem repair12335Cell17 :
    0 ≤ cap12335 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12335 (parameters ⟨17,by decide⟩)
      (scalarRow12335.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12335 ⟨17,by decide⟩ ∧
    (scalarRow12335.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12335 ⟨17,by decide⟩ + (scalarRow12335.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12335.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12335.targetFrame := by
  norm_num [cap12335, scalarRow12335, sourceIndex, cell12335, BstLean.Part263.envelope, parameters]

theorem repair12335Cell18 :
    0 ≤ cap12335 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12335 (parameters ⟨18,by decide⟩)
      (scalarRow12335.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12335 ⟨18,by decide⟩ ∧
    (scalarRow12335.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12335 ⟨18,by decide⟩ + (scalarRow12335.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12335.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12335.targetFrame := by
  norm_num [cap12335, scalarRow12335, sourceIndex, cell12335, BstLean.Part263.envelope, parameters]

theorem repair12335Cell19 :
    0 ≤ cap12335 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12335 (parameters ⟨19,by decide⟩)
      (scalarRow12335.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12335 ⟨19,by decide⟩ ∧
    (scalarRow12335.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12335 ⟨19,by decide⟩ + (scalarRow12335.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12335.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12335.targetFrame := by
  norm_num [cap12335, scalarRow12335, sourceIndex, cell12335, BstLean.Part263.envelope, parameters]

theorem repair12335Cell20 :
    0 ≤ cap12335 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12335 (parameters ⟨20,by decide⟩)
      (scalarRow12335.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12335 ⟨20,by decide⟩ ∧
    (scalarRow12335.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12335 ⟨20,by decide⟩ + (scalarRow12335.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12335.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12335.targetFrame := by
  norm_num [cap12335, scalarRow12335, sourceIndex, cell12335, BstLean.Part263.envelope, parameters]

theorem repair12335Cell21 :
    0 ≤ cap12335 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12335 (parameters ⟨21,by decide⟩)
      (scalarRow12335.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12335 ⟨21,by decide⟩ ∧
    (scalarRow12335.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12335 ⟨21,by decide⟩ + (scalarRow12335.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12335.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12335.targetFrame := by
  norm_num [cap12335, scalarRow12335, sourceIndex, cell12335, BstLean.Part263.envelope, parameters]

theorem repair12335Cell22 :
    0 ≤ cap12335 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12335 (parameters ⟨22,by decide⟩)
      (scalarRow12335.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12335 ⟨22,by decide⟩ ∧
    (scalarRow12335.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12335 ⟨22,by decide⟩ + (scalarRow12335.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12335.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12335.targetFrame := by
  norm_num [cap12335, scalarRow12335, sourceIndex, cell12335, BstLean.Part263.envelope, parameters]

theorem repair12335Cell23 :
    0 ≤ cap12335 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12335 (parameters ⟨23,by decide⟩)
      (scalarRow12335.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12335 ⟨23,by decide⟩ ∧
    (scalarRow12335.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12335 ⟨23,by decide⟩ + (scalarRow12335.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12335.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12335.targetFrame := by
  norm_num [cap12335, scalarRow12335, sourceIndex, cell12335, BstLean.Part263.envelope, parameters]

theorem repair12335Cell24 :
    0 ≤ cap12335 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12335 (parameters ⟨24,by decide⟩)
      (scalarRow12335.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12335 ⟨24,by decide⟩ ∧
    (scalarRow12335.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12335 ⟨24,by decide⟩ + (scalarRow12335.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12335.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12335.targetFrame := by
  norm_num [cap12335, scalarRow12335, sourceIndex, cell12335, BstLean.Part263.envelope, parameters]

theorem repair12335Cell25 :
    0 ≤ cap12335 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12335 (parameters ⟨25,by decide⟩)
      (scalarRow12335.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12335 ⟨25,by decide⟩ ∧
    (scalarRow12335.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12335 ⟨25,by decide⟩ + (scalarRow12335.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12335.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12335.targetFrame := by
  norm_num [cap12335, scalarRow12335, sourceIndex, cell12335, BstLean.Part263.envelope, parameters]

theorem repair12335Cell26 :
    0 ≤ cap12335 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12335 (parameters ⟨26,by decide⟩)
      (scalarRow12335.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12335 ⟨26,by decide⟩ ∧
    (scalarRow12335.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12335 ⟨26,by decide⟩ + (scalarRow12335.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12335.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12335.targetFrame := by
  norm_num [cap12335, scalarRow12335, sourceIndex, cell12335, BstLean.Part263.envelope, parameters]

theorem repair12335Cell27 :
    0 ≤ cap12335 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12335 (parameters ⟨27,by decide⟩)
      (scalarRow12335.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12335 ⟨27,by decide⟩ ∧
    (scalarRow12335.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12335 ⟨27,by decide⟩ + (scalarRow12335.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12335.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12335.targetFrame := by
  norm_num [cap12335, scalarRow12335, sourceIndex, cell12335, BstLean.Part263.envelope, parameters]

theorem repair12335Cell28 :
    0 ≤ cap12335 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12335 (parameters ⟨28,by decide⟩)
      (scalarRow12335.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12335 ⟨28,by decide⟩ ∧
    (scalarRow12335.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12335 ⟨28,by decide⟩ + (scalarRow12335.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12335.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12335.targetFrame := by
  norm_num [cap12335, scalarRow12335, sourceIndex, cell12335, BstLean.Part263.envelope, parameters]

theorem repair12335Cell29 :
    0 ≤ cap12335 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12335 (parameters ⟨29,by decide⟩)
      (scalarRow12335.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12335 ⟨29,by decide⟩ ∧
    (scalarRow12335.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12335 ⟨29,by decide⟩ + (scalarRow12335.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12335.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12335.targetFrame := by
  norm_num [cap12335, scalarRow12335, sourceIndex, cell12335, BstLean.Part263.envelope, parameters]

theorem repair12335Cell30 :
    0 ≤ cap12335 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12335 (parameters ⟨30,by decide⟩)
      (scalarRow12335.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12335 ⟨30,by decide⟩ ∧
    (scalarRow12335.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12335 ⟨30,by decide⟩ + (scalarRow12335.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12335.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12335.targetFrame := by
  norm_num [cap12335, scalarRow12335, sourceIndex, cell12335, BstLean.Part263.envelope, parameters]

theorem repair12335Cell31 :
    0 ≤ cap12335 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12335 (parameters ⟨31,by decide⟩)
      (scalarRow12335.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12335 ⟨31,by decide⟩ ∧
    (scalarRow12335.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12335 ⟨31,by decide⟩ + (scalarRow12335.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12335.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12335.targetFrame := by
  norm_num [cap12335, scalarRow12335, sourceIndex, cell12335, BstLean.Part263.envelope, parameters]

theorem repair12335Cell32 :
    0 ≤ cap12335 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12335 (parameters ⟨32,by decide⟩)
      (scalarRow12335.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12335 ⟨32,by decide⟩ ∧
    (scalarRow12335.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12335 ⟨32,by decide⟩ + (scalarRow12335.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12335.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12335.targetFrame := by
  norm_num [cap12335, scalarRow12335, sourceIndex, cell12335, BstLean.Part263.envelope, parameters]

theorem repair12335Cell33 :
    0 ≤ cap12335 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12335 (parameters ⟨33,by decide⟩)
      (scalarRow12335.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12335 ⟨33,by decide⟩ ∧
    (scalarRow12335.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12335 ⟨33,by decide⟩ + (scalarRow12335.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12335.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12335.targetFrame := by
  norm_num [cap12335, scalarRow12335, sourceIndex, cell12335, BstLean.Part263.envelope, parameters]

theorem repair12335Cell34 :
    0 ≤ cap12335 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12335 (parameters ⟨34,by decide⟩)
      (scalarRow12335.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12335 ⟨34,by decide⟩ ∧
    (scalarRow12335.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12335 ⟨34,by decide⟩ + (scalarRow12335.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12335.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12335.targetFrame := by
  norm_num [cap12335, scalarRow12335, sourceIndex, cell12335, BstLean.Part263.envelope, parameters]

theorem repair12335Cell35 :
    0 ≤ cap12335 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12335 (parameters ⟨35,by decide⟩)
      (scalarRow12335.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12335 ⟨35,by decide⟩ ∧
    (scalarRow12335.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12335 ⟨35,by decide⟩ + (scalarRow12335.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12335.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12335.targetFrame := by
  norm_num [cap12335, scalarRow12335, sourceIndex, cell12335, BstLean.Part263.envelope, parameters]

theorem repair12335Cell36 :
    0 ≤ cap12335 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12335 (parameters ⟨36,by decide⟩)
      (scalarRow12335.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12335 ⟨36,by decide⟩ ∧
    (scalarRow12335.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12335 ⟨36,by decide⟩ + (scalarRow12335.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12335.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12335.targetFrame := by
  norm_num [cap12335, scalarRow12335, sourceIndex, cell12335, BstLean.Part263.envelope, parameters]

theorem repair12335Cell37 :
    0 ≤ cap12335 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12335 (parameters ⟨37,by decide⟩)
      (scalarRow12335.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12335 ⟨37,by decide⟩ ∧
    (scalarRow12335.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12335 ⟨37,by decide⟩ + (scalarRow12335.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12335.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12335.targetFrame := by
  norm_num [cap12335, scalarRow12335, sourceIndex, cell12335, BstLean.Part263.envelope, parameters]

theorem repair12335Cell38 :
    0 ≤ cap12335 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12335 (parameters ⟨38,by decide⟩)
      (scalarRow12335.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12335 ⟨38,by decide⟩ ∧
    (scalarRow12335.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12335 ⟨38,by decide⟩ + (scalarRow12335.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12335.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12335.targetFrame := by
  norm_num [cap12335, scalarRow12335, sourceIndex, cell12335, BstLean.Part263.envelope, parameters]

theorem repair12335Cell39 :
    0 ≤ cap12335 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12335 (parameters ⟨39,by decide⟩)
      (scalarRow12335.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12335 ⟨39,by decide⟩ ∧
    (scalarRow12335.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12335 ⟨39,by decide⟩ + (scalarRow12335.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12335.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12335.targetFrame := by
  norm_num [cap12335, scalarRow12335, sourceIndex, cell12335, BstLean.Part263.envelope, parameters]

theorem repair12335Cell40 :
    0 ≤ cap12335 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12335 (parameters ⟨40,by decide⟩)
      (scalarRow12335.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12335 ⟨40,by decide⟩ ∧
    (scalarRow12335.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12335 ⟨40,by decide⟩ + (scalarRow12335.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12335.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12335.targetFrame := by
  norm_num [cap12335, scalarRow12335, sourceIndex, cell12335, BstLean.Part263.envelope, parameters]

theorem repair12335Cell41 :
    0 ≤ cap12335 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12335 (parameters ⟨41,by decide⟩)
      (scalarRow12335.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12335 ⟨41,by decide⟩ ∧
    (scalarRow12335.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12335 ⟨41,by decide⟩ + (scalarRow12335.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12335.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12335.targetFrame := by
  norm_num [cap12335, scalarRow12335, sourceIndex, cell12335, BstLean.Part263.envelope, parameters]

theorem repair12335Cell42 :
    0 ≤ cap12335 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12335 (parameters ⟨42,by decide⟩)
      (scalarRow12335.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12335 ⟨42,by decide⟩ ∧
    (scalarRow12335.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12335 ⟨42,by decide⟩ + (scalarRow12335.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12335.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12335.targetFrame := by
  norm_num [cap12335, scalarRow12335, sourceIndex, cell12335, BstLean.Part263.envelope, parameters]

theorem repair12335Cells (j : Fin 43) :
    0 ≤ cap12335 j ∧
    BstLean.Part263.envelope 12335 (parameters j) (scalarRow12335.table (sourceIndex j)).upper ≤ cap12335 j ∧
    (scalarRow12335.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12335 j + (scalarRow12335.table (sourceIndex j)).centre) /
      (scalarRow12335.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12335.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12335Cell0
  | ⟨1,_⟩ => exact repair12335Cell1
  | ⟨2,_⟩ => exact repair12335Cell2
  | ⟨3,_⟩ => exact repair12335Cell3
  | ⟨4,_⟩ => exact repair12335Cell4
  | ⟨5,_⟩ => exact repair12335Cell5
  | ⟨6,_⟩ => exact repair12335Cell6
  | ⟨7,_⟩ => exact repair12335Cell7
  | ⟨8,_⟩ => exact repair12335Cell8
  | ⟨9,_⟩ => exact repair12335Cell9
  | ⟨10,_⟩ => exact repair12335Cell10
  | ⟨11,_⟩ => exact repair12335Cell11
  | ⟨12,_⟩ => exact repair12335Cell12
  | ⟨13,_⟩ => exact repair12335Cell13
  | ⟨14,_⟩ => exact repair12335Cell14
  | ⟨15,_⟩ => exact repair12335Cell15
  | ⟨16,_⟩ => exact repair12335Cell16
  | ⟨17,_⟩ => exact repair12335Cell17
  | ⟨18,_⟩ => exact repair12335Cell18
  | ⟨19,_⟩ => exact repair12335Cell19
  | ⟨20,_⟩ => exact repair12335Cell20
  | ⟨21,_⟩ => exact repair12335Cell21
  | ⟨22,_⟩ => exact repair12335Cell22
  | ⟨23,_⟩ => exact repair12335Cell23
  | ⟨24,_⟩ => exact repair12335Cell24
  | ⟨25,_⟩ => exact repair12335Cell25
  | ⟨26,_⟩ => exact repair12335Cell26
  | ⟨27,_⟩ => exact repair12335Cell27
  | ⟨28,_⟩ => exact repair12335Cell28
  | ⟨29,_⟩ => exact repair12335Cell29
  | ⟨30,_⟩ => exact repair12335Cell30
  | ⟨31,_⟩ => exact repair12335Cell31
  | ⟨32,_⟩ => exact repair12335Cell32
  | ⟨33,_⟩ => exact repair12335Cell33
  | ⟨34,_⟩ => exact repair12335Cell34
  | ⟨35,_⟩ => exact repair12335Cell35
  | ⟨36,_⟩ => exact repair12335Cell36
  | ⟨37,_⟩ => exact repair12335Cell37
  | ⟨38,_⟩ => exact repair12335Cell38
  | ⟨39,_⟩ => exact repair12335Cell39
  | ⟨40,_⟩ => exact repair12335Cell40
  | ⟨41,_⟩ => exact repair12335Cell41
  | ⟨42,_⟩ => exact repair12335Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12335 : FrameRepair 12335 scalarRow12335 where
  cap := cap12335
  cap_nonneg := fun j => (repair12335Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12335])
  endpoint := fun j => (repair12335Cells j).2.1
  endpoint_upper := fun j => (repair12335Cells j).2.2.1
  frame := fun j => (repair12335Cells j).2.2.2

noncomputable def cap12336 : Fin 43 → ℝ
  | ⟨0,_⟩ => (275944351 / 1000000000 : ℝ)
  | ⟨1,_⟩ => (34543363 / 125000000 : ℝ)
  | ⟨2,_⟩ => (276748463 / 1000000000 : ℝ)
  | ⟨3,_⟩ => (11085961 / 40000000 : ℝ)
  | ⟨4,_⟩ => (277548597 / 1000000000 : ℝ)
  | ⟨5,_⟩ => (13897359 / 50000000 : ℝ)
  | ⟨6,_⟩ => (278344303 / 1000000000 : ℝ)
  | ⟨7,_⟩ => (6968523 / 25000000 : ℝ)
  | ⟨8,_⟩ => (139568281 / 500000000 : ℝ)
  | ⟨9,_⟩ => (8735351 / 31250000 : ℝ)
  | ⟨10,_⟩ => (69981233 / 250000000 : ℝ)
  | ⟨11,_⟩ => (1094989 / 3906250 : ℝ)
  | ⟨12,_⟩ => (1754431 / 6250000 : ℝ)
  | ⟨13,_⟩ => (281099289 / 1000000000 : ℝ)
  | ⟨14,_⟩ => (281489551 / 1000000000 : ℝ)
  | ⟨15,_⟩ => (140939357 / 500000000 : ℝ)
  | ⟨16,_⟩ => (56453387 / 200000000 : ℝ)
  | ⟨17,_⟩ => (11306169 / 40000000 : ℝ)
  | ⟨18,_⟩ => (283040577 / 1000000000 : ℝ)
  | ⟨19,_⟩ => (283426001 / 1000000000 : ℝ)
  | ⟨20,_⟩ => (141905249 / 500000000 : ℝ)
  | ⟨21,_⟩ => (284194079 / 1000000000 : ℝ)
  | ⟨22,_⟩ => (284576737 / 1000000000 : ℝ)
  | ⟨23,_⟩ => (56991597 / 200000000 : ℝ)
  | ⟨24,_⟩ => (285338821 / 1000000000 : ℝ)
  | ⟨25,_⟩ => (35714787 / 125000000 : ℝ)
  | ⟨26,_⟩ => (286097367 / 1000000000 : ℝ)
  | ⟨27,_⟩ => (1790469 / 6250000 : ℝ)
  | ⟨28,_⟩ => (35856477 / 125000000 : ℝ)
  | ⟨29,_⟩ => (143613849 / 500000000 : ℝ)
  | ⟨30,_⟩ => (143801093 / 500000000 : ℝ)
  | ⟨31,_⟩ => (287976291 / 1000000000 : ℝ)
  | ⟨32,_⟩ => (72087379 / 250000000 : ℝ)
  | ⟨33,_⟩ => (5774427 / 20000000 : ℝ)
  | ⟨34,_⟩ => (289092311 / 1000000000 : ℝ)
  | ⟨35,_⟩ => (90457 / 312500 : ℝ)
  | ⟨36,_⟩ => (289831613 / 1000000000 : ℝ)
  | ⟨37,_⟩ => (290199967 / 1000000000 : ℝ)
  | ⟨38,_⟩ => (290567457 / 1000000000 : ℝ)
  | ⟨39,_⟩ => (145466787 / 500000000 : ℝ)
  | ⟨40,_⟩ => (145649417 / 500000000 : ℝ)
  | ⟨41,_⟩ => (145831621 / 500000000 : ℝ)
  | ⟨42,_⟩ => (730067 / 2500000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12336Cell0 :
    0 ≤ cap12336 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12336 (parameters ⟨0,by decide⟩)
      (scalarRow12336.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12336 ⟨0,by decide⟩ ∧
    (scalarRow12336.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12336 ⟨0,by decide⟩ + (scalarRow12336.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12336.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12336.targetFrame := by
  norm_num [cap12336, scalarRow12336, sourceIndex, cell12336, BstLean.Part263.envelope, parameters]

theorem repair12336Cell1 :
    0 ≤ cap12336 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12336 (parameters ⟨1,by decide⟩)
      (scalarRow12336.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12336 ⟨1,by decide⟩ ∧
    (scalarRow12336.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12336 ⟨1,by decide⟩ + (scalarRow12336.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12336.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12336.targetFrame := by
  norm_num [cap12336, scalarRow12336, sourceIndex, cell12336, BstLean.Part263.envelope, parameters]

theorem repair12336Cell2 :
    0 ≤ cap12336 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12336 (parameters ⟨2,by decide⟩)
      (scalarRow12336.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12336 ⟨2,by decide⟩ ∧
    (scalarRow12336.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12336 ⟨2,by decide⟩ + (scalarRow12336.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12336.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12336.targetFrame := by
  norm_num [cap12336, scalarRow12336, sourceIndex, cell12336, BstLean.Part263.envelope, parameters]

theorem repair12336Cell3 :
    0 ≤ cap12336 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12336 (parameters ⟨3,by decide⟩)
      (scalarRow12336.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12336 ⟨3,by decide⟩ ∧
    (scalarRow12336.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12336 ⟨3,by decide⟩ + (scalarRow12336.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12336.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12336.targetFrame := by
  norm_num [cap12336, scalarRow12336, sourceIndex, cell12336, BstLean.Part263.envelope, parameters]

theorem repair12336Cell4 :
    0 ≤ cap12336 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12336 (parameters ⟨4,by decide⟩)
      (scalarRow12336.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12336 ⟨4,by decide⟩ ∧
    (scalarRow12336.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12336 ⟨4,by decide⟩ + (scalarRow12336.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12336.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12336.targetFrame := by
  norm_num [cap12336, scalarRow12336, sourceIndex, cell12336, BstLean.Part263.envelope, parameters]

theorem repair12336Cell5 :
    0 ≤ cap12336 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12336 (parameters ⟨5,by decide⟩)
      (scalarRow12336.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12336 ⟨5,by decide⟩ ∧
    (scalarRow12336.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12336 ⟨5,by decide⟩ + (scalarRow12336.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12336.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12336.targetFrame := by
  norm_num [cap12336, scalarRow12336, sourceIndex, cell12336, BstLean.Part263.envelope, parameters]

theorem repair12336Cell6 :
    0 ≤ cap12336 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12336 (parameters ⟨6,by decide⟩)
      (scalarRow12336.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12336 ⟨6,by decide⟩ ∧
    (scalarRow12336.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12336 ⟨6,by decide⟩ + (scalarRow12336.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12336.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12336.targetFrame := by
  norm_num [cap12336, scalarRow12336, sourceIndex, cell12336, BstLean.Part263.envelope, parameters]

theorem repair12336Cell7 :
    0 ≤ cap12336 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12336 (parameters ⟨7,by decide⟩)
      (scalarRow12336.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12336 ⟨7,by decide⟩ ∧
    (scalarRow12336.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12336 ⟨7,by decide⟩ + (scalarRow12336.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12336.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12336.targetFrame := by
  norm_num [cap12336, scalarRow12336, sourceIndex, cell12336, BstLean.Part263.envelope, parameters]

theorem repair12336Cell8 :
    0 ≤ cap12336 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12336 (parameters ⟨8,by decide⟩)
      (scalarRow12336.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12336 ⟨8,by decide⟩ ∧
    (scalarRow12336.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12336 ⟨8,by decide⟩ + (scalarRow12336.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12336.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12336.targetFrame := by
  norm_num [cap12336, scalarRow12336, sourceIndex, cell12336, BstLean.Part263.envelope, parameters]

theorem repair12336Cell9 :
    0 ≤ cap12336 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12336 (parameters ⟨9,by decide⟩)
      (scalarRow12336.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12336 ⟨9,by decide⟩ ∧
    (scalarRow12336.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12336 ⟨9,by decide⟩ + (scalarRow12336.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12336.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12336.targetFrame := by
  norm_num [cap12336, scalarRow12336, sourceIndex, cell12336, BstLean.Part263.envelope, parameters]

theorem repair12336Cell10 :
    0 ≤ cap12336 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12336 (parameters ⟨10,by decide⟩)
      (scalarRow12336.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12336 ⟨10,by decide⟩ ∧
    (scalarRow12336.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12336 ⟨10,by decide⟩ + (scalarRow12336.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12336.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12336.targetFrame := by
  norm_num [cap12336, scalarRow12336, sourceIndex, cell12336, BstLean.Part263.envelope, parameters]

theorem repair12336Cell11 :
    0 ≤ cap12336 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12336 (parameters ⟨11,by decide⟩)
      (scalarRow12336.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12336 ⟨11,by decide⟩ ∧
    (scalarRow12336.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12336 ⟨11,by decide⟩ + (scalarRow12336.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12336.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12336.targetFrame := by
  norm_num [cap12336, scalarRow12336, sourceIndex, cell12336, BstLean.Part263.envelope, parameters]

theorem repair12336Cell12 :
    0 ≤ cap12336 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12336 (parameters ⟨12,by decide⟩)
      (scalarRow12336.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12336 ⟨12,by decide⟩ ∧
    (scalarRow12336.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12336 ⟨12,by decide⟩ + (scalarRow12336.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12336.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12336.targetFrame := by
  norm_num [cap12336, scalarRow12336, sourceIndex, cell12336, BstLean.Part263.envelope, parameters]

theorem repair12336Cell13 :
    0 ≤ cap12336 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12336 (parameters ⟨13,by decide⟩)
      (scalarRow12336.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12336 ⟨13,by decide⟩ ∧
    (scalarRow12336.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12336 ⟨13,by decide⟩ + (scalarRow12336.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12336.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12336.targetFrame := by
  norm_num [cap12336, scalarRow12336, sourceIndex, cell12336, BstLean.Part263.envelope, parameters]

theorem repair12336Cell14 :
    0 ≤ cap12336 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12336 (parameters ⟨14,by decide⟩)
      (scalarRow12336.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12336 ⟨14,by decide⟩ ∧
    (scalarRow12336.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12336 ⟨14,by decide⟩ + (scalarRow12336.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12336.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12336.targetFrame := by
  norm_num [cap12336, scalarRow12336, sourceIndex, cell12336, BstLean.Part263.envelope, parameters]

theorem repair12336Cell15 :
    0 ≤ cap12336 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12336 (parameters ⟨15,by decide⟩)
      (scalarRow12336.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12336 ⟨15,by decide⟩ ∧
    (scalarRow12336.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12336 ⟨15,by decide⟩ + (scalarRow12336.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12336.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12336.targetFrame := by
  norm_num [cap12336, scalarRow12336, sourceIndex, cell12336, BstLean.Part263.envelope, parameters]

theorem repair12336Cell16 :
    0 ≤ cap12336 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12336 (parameters ⟨16,by decide⟩)
      (scalarRow12336.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12336 ⟨16,by decide⟩ ∧
    (scalarRow12336.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12336 ⟨16,by decide⟩ + (scalarRow12336.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12336.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12336.targetFrame := by
  norm_num [cap12336, scalarRow12336, sourceIndex, cell12336, BstLean.Part263.envelope, parameters]

theorem repair12336Cell17 :
    0 ≤ cap12336 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12336 (parameters ⟨17,by decide⟩)
      (scalarRow12336.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12336 ⟨17,by decide⟩ ∧
    (scalarRow12336.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12336 ⟨17,by decide⟩ + (scalarRow12336.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12336.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12336.targetFrame := by
  norm_num [cap12336, scalarRow12336, sourceIndex, cell12336, BstLean.Part263.envelope, parameters]

theorem repair12336Cell18 :
    0 ≤ cap12336 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12336 (parameters ⟨18,by decide⟩)
      (scalarRow12336.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12336 ⟨18,by decide⟩ ∧
    (scalarRow12336.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12336 ⟨18,by decide⟩ + (scalarRow12336.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12336.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12336.targetFrame := by
  norm_num [cap12336, scalarRow12336, sourceIndex, cell12336, BstLean.Part263.envelope, parameters]

theorem repair12336Cell19 :
    0 ≤ cap12336 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12336 (parameters ⟨19,by decide⟩)
      (scalarRow12336.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12336 ⟨19,by decide⟩ ∧
    (scalarRow12336.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12336 ⟨19,by decide⟩ + (scalarRow12336.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12336.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12336.targetFrame := by
  norm_num [cap12336, scalarRow12336, sourceIndex, cell12336, BstLean.Part263.envelope, parameters]

theorem repair12336Cell20 :
    0 ≤ cap12336 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12336 (parameters ⟨20,by decide⟩)
      (scalarRow12336.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12336 ⟨20,by decide⟩ ∧
    (scalarRow12336.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12336 ⟨20,by decide⟩ + (scalarRow12336.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12336.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12336.targetFrame := by
  norm_num [cap12336, scalarRow12336, sourceIndex, cell12336, BstLean.Part263.envelope, parameters]

theorem repair12336Cell21 :
    0 ≤ cap12336 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12336 (parameters ⟨21,by decide⟩)
      (scalarRow12336.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12336 ⟨21,by decide⟩ ∧
    (scalarRow12336.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12336 ⟨21,by decide⟩ + (scalarRow12336.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12336.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12336.targetFrame := by
  norm_num [cap12336, scalarRow12336, sourceIndex, cell12336, BstLean.Part263.envelope, parameters]

theorem repair12336Cell22 :
    0 ≤ cap12336 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12336 (parameters ⟨22,by decide⟩)
      (scalarRow12336.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12336 ⟨22,by decide⟩ ∧
    (scalarRow12336.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12336 ⟨22,by decide⟩ + (scalarRow12336.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12336.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12336.targetFrame := by
  norm_num [cap12336, scalarRow12336, sourceIndex, cell12336, BstLean.Part263.envelope, parameters]

theorem repair12336Cell23 :
    0 ≤ cap12336 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12336 (parameters ⟨23,by decide⟩)
      (scalarRow12336.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12336 ⟨23,by decide⟩ ∧
    (scalarRow12336.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12336 ⟨23,by decide⟩ + (scalarRow12336.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12336.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12336.targetFrame := by
  norm_num [cap12336, scalarRow12336, sourceIndex, cell12336, BstLean.Part263.envelope, parameters]

theorem repair12336Cell24 :
    0 ≤ cap12336 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12336 (parameters ⟨24,by decide⟩)
      (scalarRow12336.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12336 ⟨24,by decide⟩ ∧
    (scalarRow12336.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12336 ⟨24,by decide⟩ + (scalarRow12336.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12336.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12336.targetFrame := by
  norm_num [cap12336, scalarRow12336, sourceIndex, cell12336, BstLean.Part263.envelope, parameters]

theorem repair12336Cell25 :
    0 ≤ cap12336 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12336 (parameters ⟨25,by decide⟩)
      (scalarRow12336.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12336 ⟨25,by decide⟩ ∧
    (scalarRow12336.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12336 ⟨25,by decide⟩ + (scalarRow12336.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12336.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12336.targetFrame := by
  norm_num [cap12336, scalarRow12336, sourceIndex, cell12336, BstLean.Part263.envelope, parameters]

theorem repair12336Cell26 :
    0 ≤ cap12336 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12336 (parameters ⟨26,by decide⟩)
      (scalarRow12336.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12336 ⟨26,by decide⟩ ∧
    (scalarRow12336.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12336 ⟨26,by decide⟩ + (scalarRow12336.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12336.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12336.targetFrame := by
  norm_num [cap12336, scalarRow12336, sourceIndex, cell12336, BstLean.Part263.envelope, parameters]

theorem repair12336Cell27 :
    0 ≤ cap12336 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12336 (parameters ⟨27,by decide⟩)
      (scalarRow12336.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12336 ⟨27,by decide⟩ ∧
    (scalarRow12336.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12336 ⟨27,by decide⟩ + (scalarRow12336.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12336.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12336.targetFrame := by
  norm_num [cap12336, scalarRow12336, sourceIndex, cell12336, BstLean.Part263.envelope, parameters]

theorem repair12336Cell28 :
    0 ≤ cap12336 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12336 (parameters ⟨28,by decide⟩)
      (scalarRow12336.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12336 ⟨28,by decide⟩ ∧
    (scalarRow12336.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12336 ⟨28,by decide⟩ + (scalarRow12336.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12336.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12336.targetFrame := by
  norm_num [cap12336, scalarRow12336, sourceIndex, cell12336, BstLean.Part263.envelope, parameters]

theorem repair12336Cell29 :
    0 ≤ cap12336 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12336 (parameters ⟨29,by decide⟩)
      (scalarRow12336.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12336 ⟨29,by decide⟩ ∧
    (scalarRow12336.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12336 ⟨29,by decide⟩ + (scalarRow12336.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12336.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12336.targetFrame := by
  norm_num [cap12336, scalarRow12336, sourceIndex, cell12336, BstLean.Part263.envelope, parameters]

theorem repair12336Cell30 :
    0 ≤ cap12336 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12336 (parameters ⟨30,by decide⟩)
      (scalarRow12336.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12336 ⟨30,by decide⟩ ∧
    (scalarRow12336.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12336 ⟨30,by decide⟩ + (scalarRow12336.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12336.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12336.targetFrame := by
  norm_num [cap12336, scalarRow12336, sourceIndex, cell12336, BstLean.Part263.envelope, parameters]

theorem repair12336Cell31 :
    0 ≤ cap12336 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12336 (parameters ⟨31,by decide⟩)
      (scalarRow12336.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12336 ⟨31,by decide⟩ ∧
    (scalarRow12336.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12336 ⟨31,by decide⟩ + (scalarRow12336.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12336.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12336.targetFrame := by
  norm_num [cap12336, scalarRow12336, sourceIndex, cell12336, BstLean.Part263.envelope, parameters]

theorem repair12336Cell32 :
    0 ≤ cap12336 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12336 (parameters ⟨32,by decide⟩)
      (scalarRow12336.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12336 ⟨32,by decide⟩ ∧
    (scalarRow12336.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12336 ⟨32,by decide⟩ + (scalarRow12336.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12336.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12336.targetFrame := by
  norm_num [cap12336, scalarRow12336, sourceIndex, cell12336, BstLean.Part263.envelope, parameters]

theorem repair12336Cell33 :
    0 ≤ cap12336 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12336 (parameters ⟨33,by decide⟩)
      (scalarRow12336.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12336 ⟨33,by decide⟩ ∧
    (scalarRow12336.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12336 ⟨33,by decide⟩ + (scalarRow12336.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12336.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12336.targetFrame := by
  norm_num [cap12336, scalarRow12336, sourceIndex, cell12336, BstLean.Part263.envelope, parameters]

theorem repair12336Cell34 :
    0 ≤ cap12336 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12336 (parameters ⟨34,by decide⟩)
      (scalarRow12336.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12336 ⟨34,by decide⟩ ∧
    (scalarRow12336.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12336 ⟨34,by decide⟩ + (scalarRow12336.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12336.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12336.targetFrame := by
  norm_num [cap12336, scalarRow12336, sourceIndex, cell12336, BstLean.Part263.envelope, parameters]

theorem repair12336Cell35 :
    0 ≤ cap12336 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12336 (parameters ⟨35,by decide⟩)
      (scalarRow12336.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12336 ⟨35,by decide⟩ ∧
    (scalarRow12336.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12336 ⟨35,by decide⟩ + (scalarRow12336.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12336.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12336.targetFrame := by
  norm_num [cap12336, scalarRow12336, sourceIndex, cell12336, BstLean.Part263.envelope, parameters]

theorem repair12336Cell36 :
    0 ≤ cap12336 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12336 (parameters ⟨36,by decide⟩)
      (scalarRow12336.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12336 ⟨36,by decide⟩ ∧
    (scalarRow12336.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12336 ⟨36,by decide⟩ + (scalarRow12336.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12336.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12336.targetFrame := by
  norm_num [cap12336, scalarRow12336, sourceIndex, cell12336, BstLean.Part263.envelope, parameters]

theorem repair12336Cell37 :
    0 ≤ cap12336 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12336 (parameters ⟨37,by decide⟩)
      (scalarRow12336.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12336 ⟨37,by decide⟩ ∧
    (scalarRow12336.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12336 ⟨37,by decide⟩ + (scalarRow12336.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12336.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12336.targetFrame := by
  norm_num [cap12336, scalarRow12336, sourceIndex, cell12336, BstLean.Part263.envelope, parameters]

theorem repair12336Cell38 :
    0 ≤ cap12336 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12336 (parameters ⟨38,by decide⟩)
      (scalarRow12336.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12336 ⟨38,by decide⟩ ∧
    (scalarRow12336.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12336 ⟨38,by decide⟩ + (scalarRow12336.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12336.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12336.targetFrame := by
  norm_num [cap12336, scalarRow12336, sourceIndex, cell12336, BstLean.Part263.envelope, parameters]

theorem repair12336Cell39 :
    0 ≤ cap12336 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12336 (parameters ⟨39,by decide⟩)
      (scalarRow12336.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12336 ⟨39,by decide⟩ ∧
    (scalarRow12336.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12336 ⟨39,by decide⟩ + (scalarRow12336.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12336.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12336.targetFrame := by
  norm_num [cap12336, scalarRow12336, sourceIndex, cell12336, BstLean.Part263.envelope, parameters]

theorem repair12336Cell40 :
    0 ≤ cap12336 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12336 (parameters ⟨40,by decide⟩)
      (scalarRow12336.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12336 ⟨40,by decide⟩ ∧
    (scalarRow12336.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12336 ⟨40,by decide⟩ + (scalarRow12336.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12336.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12336.targetFrame := by
  norm_num [cap12336, scalarRow12336, sourceIndex, cell12336, BstLean.Part263.envelope, parameters]

theorem repair12336Cell41 :
    0 ≤ cap12336 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12336 (parameters ⟨41,by decide⟩)
      (scalarRow12336.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12336 ⟨41,by decide⟩ ∧
    (scalarRow12336.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12336 ⟨41,by decide⟩ + (scalarRow12336.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12336.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12336.targetFrame := by
  norm_num [cap12336, scalarRow12336, sourceIndex, cell12336, BstLean.Part263.envelope, parameters]

theorem repair12336Cell42 :
    0 ≤ cap12336 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12336 (parameters ⟨42,by decide⟩)
      (scalarRow12336.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12336 ⟨42,by decide⟩ ∧
    (scalarRow12336.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12336 ⟨42,by decide⟩ + (scalarRow12336.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12336.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12336.targetFrame := by
  norm_num [cap12336, scalarRow12336, sourceIndex, cell12336, BstLean.Part263.envelope, parameters]

theorem repair12336Cells (j : Fin 43) :
    0 ≤ cap12336 j ∧
    BstLean.Part263.envelope 12336 (parameters j) (scalarRow12336.table (sourceIndex j)).upper ≤ cap12336 j ∧
    (scalarRow12336.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12336 j + (scalarRow12336.table (sourceIndex j)).centre) /
      (scalarRow12336.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12336.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12336Cell0
  | ⟨1,_⟩ => exact repair12336Cell1
  | ⟨2,_⟩ => exact repair12336Cell2
  | ⟨3,_⟩ => exact repair12336Cell3
  | ⟨4,_⟩ => exact repair12336Cell4
  | ⟨5,_⟩ => exact repair12336Cell5
  | ⟨6,_⟩ => exact repair12336Cell6
  | ⟨7,_⟩ => exact repair12336Cell7
  | ⟨8,_⟩ => exact repair12336Cell8
  | ⟨9,_⟩ => exact repair12336Cell9
  | ⟨10,_⟩ => exact repair12336Cell10
  | ⟨11,_⟩ => exact repair12336Cell11
  | ⟨12,_⟩ => exact repair12336Cell12
  | ⟨13,_⟩ => exact repair12336Cell13
  | ⟨14,_⟩ => exact repair12336Cell14
  | ⟨15,_⟩ => exact repair12336Cell15
  | ⟨16,_⟩ => exact repair12336Cell16
  | ⟨17,_⟩ => exact repair12336Cell17
  | ⟨18,_⟩ => exact repair12336Cell18
  | ⟨19,_⟩ => exact repair12336Cell19
  | ⟨20,_⟩ => exact repair12336Cell20
  | ⟨21,_⟩ => exact repair12336Cell21
  | ⟨22,_⟩ => exact repair12336Cell22
  | ⟨23,_⟩ => exact repair12336Cell23
  | ⟨24,_⟩ => exact repair12336Cell24
  | ⟨25,_⟩ => exact repair12336Cell25
  | ⟨26,_⟩ => exact repair12336Cell26
  | ⟨27,_⟩ => exact repair12336Cell27
  | ⟨28,_⟩ => exact repair12336Cell28
  | ⟨29,_⟩ => exact repair12336Cell29
  | ⟨30,_⟩ => exact repair12336Cell30
  | ⟨31,_⟩ => exact repair12336Cell31
  | ⟨32,_⟩ => exact repair12336Cell32
  | ⟨33,_⟩ => exact repair12336Cell33
  | ⟨34,_⟩ => exact repair12336Cell34
  | ⟨35,_⟩ => exact repair12336Cell35
  | ⟨36,_⟩ => exact repair12336Cell36
  | ⟨37,_⟩ => exact repair12336Cell37
  | ⟨38,_⟩ => exact repair12336Cell38
  | ⟨39,_⟩ => exact repair12336Cell39
  | ⟨40,_⟩ => exact repair12336Cell40
  | ⟨41,_⟩ => exact repair12336Cell41
  | ⟨42,_⟩ => exact repair12336Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12336 : FrameRepair 12336 scalarRow12336 where
  cap := cap12336
  cap_nonneg := fun j => (repair12336Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12336])
  endpoint := fun j => (repair12336Cells j).2.1
  endpoint_upper := fun j => (repair12336Cells j).2.2.1
  frame := fun j => (repair12336Cells j).2.2.2

noncomputable def cap12337 : Fin 43 → ℝ
  | ⟨0,_⟩ => (68986069 / 250000000 : ℝ)
  | ⟨1,_⟩ => (276346823 / 1000000000 : ℝ)
  | ⟨2,_⟩ => (2213987 / 8000000 : ℝ)
  | ⟨3,_⟩ => (27714893 / 100000000 : ℝ)
  | ⟨4,_⟩ => (17346781 / 62500000 : ℝ)
  | ⟨5,_⟩ => (277947073 / 1000000000 : ℝ)
  | ⟨6,_⟩ => (278344189 / 1000000000 : ℝ)
  | ⟨7,_⟩ => (174213 / 625000 : ℝ)
  | ⟨8,_⟩ => (69784109 / 250000000 : ℝ)
  | ⟨9,_⟩ => (2795311 / 10000000 : ℝ)
  | ⟨10,_⟩ => (279924793 / 1000000000 : ℝ)
  | ⟨11,_⟩ => (280317039 / 1000000000 : ℝ)
  | ⟨12,_⟩ => (35088601 / 125000000 : ℝ)
  | ⟨13,_⟩ => (281099131 / 1000000000 : ℝ)
  | ⟨14,_⟩ => (281489387 / 1000000000 : ℝ)
  | ⟨15,_⟩ => (17617409 / 62500000 : ℝ)
  | ⟨16,_⟩ => (282266759 / 1000000000 : ℝ)
  | ⟨17,_⟩ => (282654043 / 1000000000 : ℝ)
  | ⟨18,_⟩ => (70760097 / 250000000 : ℝ)
  | ⟨19,_⟩ => (141712903 / 500000000 : ℝ)
  | ⟨20,_⟩ => (283810297 / 1000000000 : ℝ)
  | ⟨21,_⟩ => (17762117 / 62500000 : ℝ)
  | ⟨22,_⟩ => (71144131 / 250000000 : ℝ)
  | ⟨23,_⟩ => (56991553 / 200000000 : ℝ)
  | ⟨24,_⟩ => (57067719 / 200000000 : ℝ)
  | ⟨25,_⟩ => (17857379 / 62500000 : ℝ)
  | ⟨26,_⟩ => (286097129 / 1000000000 : ℝ)
  | ⟨27,_⟩ => (71618699 / 250000000 : ℝ)
  | ⟨28,_⟩ => (143425783 / 500000000 : ℝ)
  | ⟨29,_⟩ => (143613721 / 500000000 : ℝ)
  | ⟨30,_⟩ => (71900481 / 250000000 : ℝ)
  | ⟨31,_⟩ => (287976023 / 1000000000 : ℝ)
  | ⟨32,_⟩ => (288349241 / 1000000000 : ℝ)
  | ⟨33,_⟩ => (28872107 / 100000000 : ℝ)
  | ⟨34,_⟩ => (36136503 / 125000000 : ℝ)
  | ⟨35,_⟩ => (289462107 / 1000000000 : ℝ)
  | ⟨36,_⟩ => (144915657 / 500000000 : ℝ)
  | ⟨37,_⟩ => (290199663 / 1000000000 : ℝ)
  | ⟨38,_⟩ => (145283573 / 500000000 : ℝ)
  | ⟨39,_⟩ => (145466629 / 500000000 : ℝ)
  | ⟨40,_⟩ => (18206157 / 62500000 : ℝ)
  | ⟨41,_⟩ => (145831457 / 500000000 : ℝ)
  | ⟨42,_⟩ => (146013233 / 500000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12337Cell0 :
    0 ≤ cap12337 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12337 (parameters ⟨0,by decide⟩)
      (scalarRow12337.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12337 ⟨0,by decide⟩ ∧
    (scalarRow12337.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12337 ⟨0,by decide⟩ + (scalarRow12337.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12337.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12337.targetFrame := by
  norm_num [cap12337, scalarRow12337, sourceIndex, cell12337, BstLean.Part263.envelope, parameters]

theorem repair12337Cell1 :
    0 ≤ cap12337 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12337 (parameters ⟨1,by decide⟩)
      (scalarRow12337.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12337 ⟨1,by decide⟩ ∧
    (scalarRow12337.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12337 ⟨1,by decide⟩ + (scalarRow12337.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12337.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12337.targetFrame := by
  norm_num [cap12337, scalarRow12337, sourceIndex, cell12337, BstLean.Part263.envelope, parameters]

theorem repair12337Cell2 :
    0 ≤ cap12337 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12337 (parameters ⟨2,by decide⟩)
      (scalarRow12337.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12337 ⟨2,by decide⟩ ∧
    (scalarRow12337.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12337 ⟨2,by decide⟩ + (scalarRow12337.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12337.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12337.targetFrame := by
  norm_num [cap12337, scalarRow12337, sourceIndex, cell12337, BstLean.Part263.envelope, parameters]

theorem repair12337Cell3 :
    0 ≤ cap12337 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12337 (parameters ⟨3,by decide⟩)
      (scalarRow12337.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12337 ⟨3,by decide⟩ ∧
    (scalarRow12337.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12337 ⟨3,by decide⟩ + (scalarRow12337.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12337.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12337.targetFrame := by
  norm_num [cap12337, scalarRow12337, sourceIndex, cell12337, BstLean.Part263.envelope, parameters]

theorem repair12337Cell4 :
    0 ≤ cap12337 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12337 (parameters ⟨4,by decide⟩)
      (scalarRow12337.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12337 ⟨4,by decide⟩ ∧
    (scalarRow12337.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12337 ⟨4,by decide⟩ + (scalarRow12337.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12337.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12337.targetFrame := by
  norm_num [cap12337, scalarRow12337, sourceIndex, cell12337, BstLean.Part263.envelope, parameters]

theorem repair12337Cell5 :
    0 ≤ cap12337 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12337 (parameters ⟨5,by decide⟩)
      (scalarRow12337.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12337 ⟨5,by decide⟩ ∧
    (scalarRow12337.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12337 ⟨5,by decide⟩ + (scalarRow12337.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12337.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12337.targetFrame := by
  norm_num [cap12337, scalarRow12337, sourceIndex, cell12337, BstLean.Part263.envelope, parameters]

theorem repair12337Cell6 :
    0 ≤ cap12337 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12337 (parameters ⟨6,by decide⟩)
      (scalarRow12337.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12337 ⟨6,by decide⟩ ∧
    (scalarRow12337.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12337 ⟨6,by decide⟩ + (scalarRow12337.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12337.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12337.targetFrame := by
  norm_num [cap12337, scalarRow12337, sourceIndex, cell12337, BstLean.Part263.envelope, parameters]

theorem repair12337Cell7 :
    0 ≤ cap12337 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12337 (parameters ⟨7,by decide⟩)
      (scalarRow12337.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12337 ⟨7,by decide⟩ ∧
    (scalarRow12337.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12337 ⟨7,by decide⟩ + (scalarRow12337.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12337.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12337.targetFrame := by
  norm_num [cap12337, scalarRow12337, sourceIndex, cell12337, BstLean.Part263.envelope, parameters]

theorem repair12337Cell8 :
    0 ≤ cap12337 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12337 (parameters ⟨8,by decide⟩)
      (scalarRow12337.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12337 ⟨8,by decide⟩ ∧
    (scalarRow12337.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12337 ⟨8,by decide⟩ + (scalarRow12337.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12337.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12337.targetFrame := by
  norm_num [cap12337, scalarRow12337, sourceIndex, cell12337, BstLean.Part263.envelope, parameters]

theorem repair12337Cell9 :
    0 ≤ cap12337 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12337 (parameters ⟨9,by decide⟩)
      (scalarRow12337.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12337 ⟨9,by decide⟩ ∧
    (scalarRow12337.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12337 ⟨9,by decide⟩ + (scalarRow12337.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12337.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12337.targetFrame := by
  norm_num [cap12337, scalarRow12337, sourceIndex, cell12337, BstLean.Part263.envelope, parameters]

theorem repair12337Cell10 :
    0 ≤ cap12337 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12337 (parameters ⟨10,by decide⟩)
      (scalarRow12337.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12337 ⟨10,by decide⟩ ∧
    (scalarRow12337.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12337 ⟨10,by decide⟩ + (scalarRow12337.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12337.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12337.targetFrame := by
  norm_num [cap12337, scalarRow12337, sourceIndex, cell12337, BstLean.Part263.envelope, parameters]

theorem repair12337Cell11 :
    0 ≤ cap12337 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12337 (parameters ⟨11,by decide⟩)
      (scalarRow12337.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12337 ⟨11,by decide⟩ ∧
    (scalarRow12337.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12337 ⟨11,by decide⟩ + (scalarRow12337.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12337.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12337.targetFrame := by
  norm_num [cap12337, scalarRow12337, sourceIndex, cell12337, BstLean.Part263.envelope, parameters]

theorem repair12337Cell12 :
    0 ≤ cap12337 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12337 (parameters ⟨12,by decide⟩)
      (scalarRow12337.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12337 ⟨12,by decide⟩ ∧
    (scalarRow12337.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12337 ⟨12,by decide⟩ + (scalarRow12337.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12337.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12337.targetFrame := by
  norm_num [cap12337, scalarRow12337, sourceIndex, cell12337, BstLean.Part263.envelope, parameters]

theorem repair12337Cell13 :
    0 ≤ cap12337 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12337 (parameters ⟨13,by decide⟩)
      (scalarRow12337.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12337 ⟨13,by decide⟩ ∧
    (scalarRow12337.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12337 ⟨13,by decide⟩ + (scalarRow12337.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12337.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12337.targetFrame := by
  norm_num [cap12337, scalarRow12337, sourceIndex, cell12337, BstLean.Part263.envelope, parameters]

theorem repair12337Cell14 :
    0 ≤ cap12337 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12337 (parameters ⟨14,by decide⟩)
      (scalarRow12337.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12337 ⟨14,by decide⟩ ∧
    (scalarRow12337.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12337 ⟨14,by decide⟩ + (scalarRow12337.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12337.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12337.targetFrame := by
  norm_num [cap12337, scalarRow12337, sourceIndex, cell12337, BstLean.Part263.envelope, parameters]

theorem repair12337Cell15 :
    0 ≤ cap12337 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12337 (parameters ⟨15,by decide⟩)
      (scalarRow12337.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12337 ⟨15,by decide⟩ ∧
    (scalarRow12337.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12337 ⟨15,by decide⟩ + (scalarRow12337.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12337.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12337.targetFrame := by
  norm_num [cap12337, scalarRow12337, sourceIndex, cell12337, BstLean.Part263.envelope, parameters]

theorem repair12337Cell16 :
    0 ≤ cap12337 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12337 (parameters ⟨16,by decide⟩)
      (scalarRow12337.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12337 ⟨16,by decide⟩ ∧
    (scalarRow12337.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12337 ⟨16,by decide⟩ + (scalarRow12337.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12337.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12337.targetFrame := by
  norm_num [cap12337, scalarRow12337, sourceIndex, cell12337, BstLean.Part263.envelope, parameters]

theorem repair12337Cell17 :
    0 ≤ cap12337 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12337 (parameters ⟨17,by decide⟩)
      (scalarRow12337.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12337 ⟨17,by decide⟩ ∧
    (scalarRow12337.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12337 ⟨17,by decide⟩ + (scalarRow12337.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12337.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12337.targetFrame := by
  norm_num [cap12337, scalarRow12337, sourceIndex, cell12337, BstLean.Part263.envelope, parameters]

theorem repair12337Cell18 :
    0 ≤ cap12337 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12337 (parameters ⟨18,by decide⟩)
      (scalarRow12337.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12337 ⟨18,by decide⟩ ∧
    (scalarRow12337.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12337 ⟨18,by decide⟩ + (scalarRow12337.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12337.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12337.targetFrame := by
  norm_num [cap12337, scalarRow12337, sourceIndex, cell12337, BstLean.Part263.envelope, parameters]

theorem repair12337Cell19 :
    0 ≤ cap12337 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12337 (parameters ⟨19,by decide⟩)
      (scalarRow12337.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12337 ⟨19,by decide⟩ ∧
    (scalarRow12337.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12337 ⟨19,by decide⟩ + (scalarRow12337.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12337.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12337.targetFrame := by
  norm_num [cap12337, scalarRow12337, sourceIndex, cell12337, BstLean.Part263.envelope, parameters]

theorem repair12337Cell20 :
    0 ≤ cap12337 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12337 (parameters ⟨20,by decide⟩)
      (scalarRow12337.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12337 ⟨20,by decide⟩ ∧
    (scalarRow12337.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12337 ⟨20,by decide⟩ + (scalarRow12337.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12337.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12337.targetFrame := by
  norm_num [cap12337, scalarRow12337, sourceIndex, cell12337, BstLean.Part263.envelope, parameters]

theorem repair12337Cell21 :
    0 ≤ cap12337 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12337 (parameters ⟨21,by decide⟩)
      (scalarRow12337.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12337 ⟨21,by decide⟩ ∧
    (scalarRow12337.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12337 ⟨21,by decide⟩ + (scalarRow12337.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12337.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12337.targetFrame := by
  norm_num [cap12337, scalarRow12337, sourceIndex, cell12337, BstLean.Part263.envelope, parameters]

theorem repair12337Cell22 :
    0 ≤ cap12337 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12337 (parameters ⟨22,by decide⟩)
      (scalarRow12337.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12337 ⟨22,by decide⟩ ∧
    (scalarRow12337.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12337 ⟨22,by decide⟩ + (scalarRow12337.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12337.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12337.targetFrame := by
  norm_num [cap12337, scalarRow12337, sourceIndex, cell12337, BstLean.Part263.envelope, parameters]

theorem repair12337Cell23 :
    0 ≤ cap12337 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12337 (parameters ⟨23,by decide⟩)
      (scalarRow12337.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12337 ⟨23,by decide⟩ ∧
    (scalarRow12337.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12337 ⟨23,by decide⟩ + (scalarRow12337.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12337.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12337.targetFrame := by
  norm_num [cap12337, scalarRow12337, sourceIndex, cell12337, BstLean.Part263.envelope, parameters]

theorem repair12337Cell24 :
    0 ≤ cap12337 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12337 (parameters ⟨24,by decide⟩)
      (scalarRow12337.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12337 ⟨24,by decide⟩ ∧
    (scalarRow12337.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12337 ⟨24,by decide⟩ + (scalarRow12337.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12337.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12337.targetFrame := by
  norm_num [cap12337, scalarRow12337, sourceIndex, cell12337, BstLean.Part263.envelope, parameters]

theorem repair12337Cell25 :
    0 ≤ cap12337 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12337 (parameters ⟨25,by decide⟩)
      (scalarRow12337.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12337 ⟨25,by decide⟩ ∧
    (scalarRow12337.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12337 ⟨25,by decide⟩ + (scalarRow12337.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12337.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12337.targetFrame := by
  norm_num [cap12337, scalarRow12337, sourceIndex, cell12337, BstLean.Part263.envelope, parameters]

theorem repair12337Cell26 :
    0 ≤ cap12337 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12337 (parameters ⟨26,by decide⟩)
      (scalarRow12337.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12337 ⟨26,by decide⟩ ∧
    (scalarRow12337.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12337 ⟨26,by decide⟩ + (scalarRow12337.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12337.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12337.targetFrame := by
  norm_num [cap12337, scalarRow12337, sourceIndex, cell12337, BstLean.Part263.envelope, parameters]

theorem repair12337Cell27 :
    0 ≤ cap12337 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12337 (parameters ⟨27,by decide⟩)
      (scalarRow12337.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12337 ⟨27,by decide⟩ ∧
    (scalarRow12337.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12337 ⟨27,by decide⟩ + (scalarRow12337.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12337.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12337.targetFrame := by
  norm_num [cap12337, scalarRow12337, sourceIndex, cell12337, BstLean.Part263.envelope, parameters]

theorem repair12337Cell28 :
    0 ≤ cap12337 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12337 (parameters ⟨28,by decide⟩)
      (scalarRow12337.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12337 ⟨28,by decide⟩ ∧
    (scalarRow12337.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12337 ⟨28,by decide⟩ + (scalarRow12337.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12337.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12337.targetFrame := by
  norm_num [cap12337, scalarRow12337, sourceIndex, cell12337, BstLean.Part263.envelope, parameters]

theorem repair12337Cell29 :
    0 ≤ cap12337 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12337 (parameters ⟨29,by decide⟩)
      (scalarRow12337.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12337 ⟨29,by decide⟩ ∧
    (scalarRow12337.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12337 ⟨29,by decide⟩ + (scalarRow12337.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12337.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12337.targetFrame := by
  norm_num [cap12337, scalarRow12337, sourceIndex, cell12337, BstLean.Part263.envelope, parameters]

theorem repair12337Cell30 :
    0 ≤ cap12337 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12337 (parameters ⟨30,by decide⟩)
      (scalarRow12337.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12337 ⟨30,by decide⟩ ∧
    (scalarRow12337.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12337 ⟨30,by decide⟩ + (scalarRow12337.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12337.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12337.targetFrame := by
  norm_num [cap12337, scalarRow12337, sourceIndex, cell12337, BstLean.Part263.envelope, parameters]

theorem repair12337Cell31 :
    0 ≤ cap12337 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12337 (parameters ⟨31,by decide⟩)
      (scalarRow12337.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12337 ⟨31,by decide⟩ ∧
    (scalarRow12337.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12337 ⟨31,by decide⟩ + (scalarRow12337.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12337.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12337.targetFrame := by
  norm_num [cap12337, scalarRow12337, sourceIndex, cell12337, BstLean.Part263.envelope, parameters]

theorem repair12337Cell32 :
    0 ≤ cap12337 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12337 (parameters ⟨32,by decide⟩)
      (scalarRow12337.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12337 ⟨32,by decide⟩ ∧
    (scalarRow12337.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12337 ⟨32,by decide⟩ + (scalarRow12337.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12337.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12337.targetFrame := by
  norm_num [cap12337, scalarRow12337, sourceIndex, cell12337, BstLean.Part263.envelope, parameters]

theorem repair12337Cell33 :
    0 ≤ cap12337 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12337 (parameters ⟨33,by decide⟩)
      (scalarRow12337.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12337 ⟨33,by decide⟩ ∧
    (scalarRow12337.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12337 ⟨33,by decide⟩ + (scalarRow12337.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12337.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12337.targetFrame := by
  norm_num [cap12337, scalarRow12337, sourceIndex, cell12337, BstLean.Part263.envelope, parameters]

theorem repair12337Cell34 :
    0 ≤ cap12337 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12337 (parameters ⟨34,by decide⟩)
      (scalarRow12337.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12337 ⟨34,by decide⟩ ∧
    (scalarRow12337.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12337 ⟨34,by decide⟩ + (scalarRow12337.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12337.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12337.targetFrame := by
  norm_num [cap12337, scalarRow12337, sourceIndex, cell12337, BstLean.Part263.envelope, parameters]

theorem repair12337Cell35 :
    0 ≤ cap12337 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12337 (parameters ⟨35,by decide⟩)
      (scalarRow12337.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12337 ⟨35,by decide⟩ ∧
    (scalarRow12337.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12337 ⟨35,by decide⟩ + (scalarRow12337.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12337.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12337.targetFrame := by
  norm_num [cap12337, scalarRow12337, sourceIndex, cell12337, BstLean.Part263.envelope, parameters]

theorem repair12337Cell36 :
    0 ≤ cap12337 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12337 (parameters ⟨36,by decide⟩)
      (scalarRow12337.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12337 ⟨36,by decide⟩ ∧
    (scalarRow12337.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12337 ⟨36,by decide⟩ + (scalarRow12337.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12337.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12337.targetFrame := by
  norm_num [cap12337, scalarRow12337, sourceIndex, cell12337, BstLean.Part263.envelope, parameters]

theorem repair12337Cell37 :
    0 ≤ cap12337 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12337 (parameters ⟨37,by decide⟩)
      (scalarRow12337.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12337 ⟨37,by decide⟩ ∧
    (scalarRow12337.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12337 ⟨37,by decide⟩ + (scalarRow12337.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12337.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12337.targetFrame := by
  norm_num [cap12337, scalarRow12337, sourceIndex, cell12337, BstLean.Part263.envelope, parameters]

theorem repair12337Cell38 :
    0 ≤ cap12337 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12337 (parameters ⟨38,by decide⟩)
      (scalarRow12337.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12337 ⟨38,by decide⟩ ∧
    (scalarRow12337.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12337 ⟨38,by decide⟩ + (scalarRow12337.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12337.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12337.targetFrame := by
  norm_num [cap12337, scalarRow12337, sourceIndex, cell12337, BstLean.Part263.envelope, parameters]

theorem repair12337Cell39 :
    0 ≤ cap12337 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12337 (parameters ⟨39,by decide⟩)
      (scalarRow12337.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12337 ⟨39,by decide⟩ ∧
    (scalarRow12337.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12337 ⟨39,by decide⟩ + (scalarRow12337.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12337.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12337.targetFrame := by
  norm_num [cap12337, scalarRow12337, sourceIndex, cell12337, BstLean.Part263.envelope, parameters]

theorem repair12337Cell40 :
    0 ≤ cap12337 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12337 (parameters ⟨40,by decide⟩)
      (scalarRow12337.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12337 ⟨40,by decide⟩ ∧
    (scalarRow12337.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12337 ⟨40,by decide⟩ + (scalarRow12337.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12337.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12337.targetFrame := by
  norm_num [cap12337, scalarRow12337, sourceIndex, cell12337, BstLean.Part263.envelope, parameters]

theorem repair12337Cell41 :
    0 ≤ cap12337 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12337 (parameters ⟨41,by decide⟩)
      (scalarRow12337.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12337 ⟨41,by decide⟩ ∧
    (scalarRow12337.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12337 ⟨41,by decide⟩ + (scalarRow12337.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12337.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12337.targetFrame := by
  norm_num [cap12337, scalarRow12337, sourceIndex, cell12337, BstLean.Part263.envelope, parameters]

theorem repair12337Cell42 :
    0 ≤ cap12337 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12337 (parameters ⟨42,by decide⟩)
      (scalarRow12337.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12337 ⟨42,by decide⟩ ∧
    (scalarRow12337.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12337 ⟨42,by decide⟩ + (scalarRow12337.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12337.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12337.targetFrame := by
  norm_num [cap12337, scalarRow12337, sourceIndex, cell12337, BstLean.Part263.envelope, parameters]

theorem repair12337Cells (j : Fin 43) :
    0 ≤ cap12337 j ∧
    BstLean.Part263.envelope 12337 (parameters j) (scalarRow12337.table (sourceIndex j)).upper ≤ cap12337 j ∧
    (scalarRow12337.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12337 j + (scalarRow12337.table (sourceIndex j)).centre) /
      (scalarRow12337.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12337.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12337Cell0
  | ⟨1,_⟩ => exact repair12337Cell1
  | ⟨2,_⟩ => exact repair12337Cell2
  | ⟨3,_⟩ => exact repair12337Cell3
  | ⟨4,_⟩ => exact repair12337Cell4
  | ⟨5,_⟩ => exact repair12337Cell5
  | ⟨6,_⟩ => exact repair12337Cell6
  | ⟨7,_⟩ => exact repair12337Cell7
  | ⟨8,_⟩ => exact repair12337Cell8
  | ⟨9,_⟩ => exact repair12337Cell9
  | ⟨10,_⟩ => exact repair12337Cell10
  | ⟨11,_⟩ => exact repair12337Cell11
  | ⟨12,_⟩ => exact repair12337Cell12
  | ⟨13,_⟩ => exact repair12337Cell13
  | ⟨14,_⟩ => exact repair12337Cell14
  | ⟨15,_⟩ => exact repair12337Cell15
  | ⟨16,_⟩ => exact repair12337Cell16
  | ⟨17,_⟩ => exact repair12337Cell17
  | ⟨18,_⟩ => exact repair12337Cell18
  | ⟨19,_⟩ => exact repair12337Cell19
  | ⟨20,_⟩ => exact repair12337Cell20
  | ⟨21,_⟩ => exact repair12337Cell21
  | ⟨22,_⟩ => exact repair12337Cell22
  | ⟨23,_⟩ => exact repair12337Cell23
  | ⟨24,_⟩ => exact repair12337Cell24
  | ⟨25,_⟩ => exact repair12337Cell25
  | ⟨26,_⟩ => exact repair12337Cell26
  | ⟨27,_⟩ => exact repair12337Cell27
  | ⟨28,_⟩ => exact repair12337Cell28
  | ⟨29,_⟩ => exact repair12337Cell29
  | ⟨30,_⟩ => exact repair12337Cell30
  | ⟨31,_⟩ => exact repair12337Cell31
  | ⟨32,_⟩ => exact repair12337Cell32
  | ⟨33,_⟩ => exact repair12337Cell33
  | ⟨34,_⟩ => exact repair12337Cell34
  | ⟨35,_⟩ => exact repair12337Cell35
  | ⟨36,_⟩ => exact repair12337Cell36
  | ⟨37,_⟩ => exact repair12337Cell37
  | ⟨38,_⟩ => exact repair12337Cell38
  | ⟨39,_⟩ => exact repair12337Cell39
  | ⟨40,_⟩ => exact repair12337Cell40
  | ⟨41,_⟩ => exact repair12337Cell41
  | ⟨42,_⟩ => exact repair12337Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12337 : FrameRepair 12337 scalarRow12337 where
  cap := cap12337
  cap_nonneg := fun j => (repair12337Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12337])
  endpoint := fun j => (repair12337Cells j).2.1
  endpoint_upper := fun j => (repair12337Cells j).2.2.1
  frame := fun j => (repair12337Cells j).2.2.2

noncomputable def cap12338 : Fin 43 → ℝ
  | ⟨0,_⟩ => (137972101 / 500000000 : ℝ)
  | ⟨1,_⟩ => (276346741 / 1000000000 : ℝ)
  | ⟨2,_⟩ => (276748287 / 1000000000 : ℝ)
  | ⟨3,_⟩ => (69287209 / 250000000 : ℝ)
  | ⟨4,_⟩ => (69387099 / 250000000 : ℝ)
  | ⟨5,_⟩ => (138973483 / 500000000 : ℝ)
  | ⟨6,_⟩ => (69586019 / 250000000 : ℝ)
  | ⟨7,_⟩ => (6968517 / 25000000 : ℝ)
  | ⟨8,_⟩ => (27913631 / 100000000 : ℝ)
  | ⟨9,_⟩ => (279530967 / 1000000000 : ℝ)
  | ⟨10,_⟩ => (55984931 / 200000000 : ℝ)
  | ⟨11,_⟩ => (140158447 / 500000000 : ℝ)
  | ⟨12,_⟩ => (280708657 / 1000000000 : ℝ)
  | ⟨13,_⟩ => (281098973 / 1000000000 : ℝ)
  | ⟨14,_⟩ => (281489223 / 1000000000 : ℝ)
  | ⟨15,_⟩ => (140939187 / 500000000 : ℝ)
  | ⟨16,_⟩ => (141133291 / 500000000 : ℝ)
  | ⟨17,_⟩ => (14132693 / 50000000 : ℝ)
  | ⟨18,_⟩ => (283040199 / 1000000000 : ℝ)
  | ⟨19,_⟩ => (283425611 / 1000000000 : ℝ)
  | ⟨20,_⟩ => (17738131 / 62500000 : ℝ)
  | ⟨21,_⟩ => (56838733 / 200000000 : ℝ)
  | ⟨22,_⟩ => (28457631 / 100000000 : ℝ)
  | ⟨23,_⟩ => (142478773 / 500000000 : ℝ)
  | ⟨24,_⟩ => (285338369 / 1000000000 : ℝ)
  | ⟨25,_⟩ => (35714729 / 125000000 : ℝ)
  | ⟨26,_⟩ => (286096891 / 1000000000 : ℝ)
  | ⟨27,_⟩ => (35809319 / 125000000 : ℝ)
  | ⟨28,_⟩ => (71712829 / 250000000 : ℝ)
  | ⟨29,_⟩ => (57445437 / 200000000 : ℝ)
  | ⟨30,_⟩ => (143800831 / 500000000 : ℝ)
  | ⟨31,_⟩ => (57595151 / 200000000 : ℝ)
  | ⟨32,_⟩ => (288348967 / 1000000000 : ℝ)
  | ⟨33,_⟩ => (28872079 / 100000000 : ℝ)
  | ⟨34,_⟩ => (144545869 / 500000000 : ℝ)
  | ⟨35,_⟩ => (57892363 / 200000000 : ℝ)
  | ⟨36,_⟩ => (36228877 / 125000000 : ℝ)
  | ⟨37,_⟩ => (145099679 / 500000000 : ℝ)
  | ⟨38,_⟩ => (72641709 / 250000000 : ℝ)
  | ⟨39,_⟩ => (145466471 / 500000000 : ℝ)
  | ⟨40,_⟩ => (29129819 / 100000000 : ℝ)
  | ⟨41,_⟩ => (145831293 / 500000000 : ℝ)
  | ⟨42,_⟩ => (73006533 / 250000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12338Cell0 :
    0 ≤ cap12338 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12338 (parameters ⟨0,by decide⟩)
      (scalarRow12338.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12338 ⟨0,by decide⟩ ∧
    (scalarRow12338.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12338 ⟨0,by decide⟩ + (scalarRow12338.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12338.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12338.targetFrame := by
  norm_num [cap12338, scalarRow12338, sourceIndex, cell12338, BstLean.Part263.envelope, parameters]

theorem repair12338Cell1 :
    0 ≤ cap12338 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12338 (parameters ⟨1,by decide⟩)
      (scalarRow12338.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12338 ⟨1,by decide⟩ ∧
    (scalarRow12338.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12338 ⟨1,by decide⟩ + (scalarRow12338.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12338.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12338.targetFrame := by
  norm_num [cap12338, scalarRow12338, sourceIndex, cell12338, BstLean.Part263.envelope, parameters]

theorem repair12338Cell2 :
    0 ≤ cap12338 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12338 (parameters ⟨2,by decide⟩)
      (scalarRow12338.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12338 ⟨2,by decide⟩ ∧
    (scalarRow12338.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12338 ⟨2,by decide⟩ + (scalarRow12338.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12338.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12338.targetFrame := by
  norm_num [cap12338, scalarRow12338, sourceIndex, cell12338, BstLean.Part263.envelope, parameters]

theorem repair12338Cell3 :
    0 ≤ cap12338 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12338 (parameters ⟨3,by decide⟩)
      (scalarRow12338.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12338 ⟨3,by decide⟩ ∧
    (scalarRow12338.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12338 ⟨3,by decide⟩ + (scalarRow12338.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12338.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12338.targetFrame := by
  norm_num [cap12338, scalarRow12338, sourceIndex, cell12338, BstLean.Part263.envelope, parameters]

theorem repair12338Cell4 :
    0 ≤ cap12338 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12338 (parameters ⟨4,by decide⟩)
      (scalarRow12338.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12338 ⟨4,by decide⟩ ∧
    (scalarRow12338.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12338 ⟨4,by decide⟩ + (scalarRow12338.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12338.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12338.targetFrame := by
  norm_num [cap12338, scalarRow12338, sourceIndex, cell12338, BstLean.Part263.envelope, parameters]

theorem repair12338Cell5 :
    0 ≤ cap12338 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12338 (parameters ⟨5,by decide⟩)
      (scalarRow12338.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12338 ⟨5,by decide⟩ ∧
    (scalarRow12338.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12338 ⟨5,by decide⟩ + (scalarRow12338.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12338.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12338.targetFrame := by
  norm_num [cap12338, scalarRow12338, sourceIndex, cell12338, BstLean.Part263.envelope, parameters]

theorem repair12338Cell6 :
    0 ≤ cap12338 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12338 (parameters ⟨6,by decide⟩)
      (scalarRow12338.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12338 ⟨6,by decide⟩ ∧
    (scalarRow12338.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12338 ⟨6,by decide⟩ + (scalarRow12338.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12338.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12338.targetFrame := by
  norm_num [cap12338, scalarRow12338, sourceIndex, cell12338, BstLean.Part263.envelope, parameters]

theorem repair12338Cell7 :
    0 ≤ cap12338 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12338 (parameters ⟨7,by decide⟩)
      (scalarRow12338.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12338 ⟨7,by decide⟩ ∧
    (scalarRow12338.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12338 ⟨7,by decide⟩ + (scalarRow12338.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12338.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12338.targetFrame := by
  norm_num [cap12338, scalarRow12338, sourceIndex, cell12338, BstLean.Part263.envelope, parameters]

theorem repair12338Cell8 :
    0 ≤ cap12338 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12338 (parameters ⟨8,by decide⟩)
      (scalarRow12338.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12338 ⟨8,by decide⟩ ∧
    (scalarRow12338.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12338 ⟨8,by decide⟩ + (scalarRow12338.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12338.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12338.targetFrame := by
  norm_num [cap12338, scalarRow12338, sourceIndex, cell12338, BstLean.Part263.envelope, parameters]

theorem repair12338Cell9 :
    0 ≤ cap12338 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12338 (parameters ⟨9,by decide⟩)
      (scalarRow12338.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12338 ⟨9,by decide⟩ ∧
    (scalarRow12338.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12338 ⟨9,by decide⟩ + (scalarRow12338.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12338.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12338.targetFrame := by
  norm_num [cap12338, scalarRow12338, sourceIndex, cell12338, BstLean.Part263.envelope, parameters]

theorem repair12338Cell10 :
    0 ≤ cap12338 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12338 (parameters ⟨10,by decide⟩)
      (scalarRow12338.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12338 ⟨10,by decide⟩ ∧
    (scalarRow12338.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12338 ⟨10,by decide⟩ + (scalarRow12338.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12338.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12338.targetFrame := by
  norm_num [cap12338, scalarRow12338, sourceIndex, cell12338, BstLean.Part263.envelope, parameters]

theorem repair12338Cell11 :
    0 ≤ cap12338 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12338 (parameters ⟨11,by decide⟩)
      (scalarRow12338.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12338 ⟨11,by decide⟩ ∧
    (scalarRow12338.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12338 ⟨11,by decide⟩ + (scalarRow12338.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12338.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12338.targetFrame := by
  norm_num [cap12338, scalarRow12338, sourceIndex, cell12338, BstLean.Part263.envelope, parameters]

theorem repair12338Cell12 :
    0 ≤ cap12338 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12338 (parameters ⟨12,by decide⟩)
      (scalarRow12338.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12338 ⟨12,by decide⟩ ∧
    (scalarRow12338.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12338 ⟨12,by decide⟩ + (scalarRow12338.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12338.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12338.targetFrame := by
  norm_num [cap12338, scalarRow12338, sourceIndex, cell12338, BstLean.Part263.envelope, parameters]

theorem repair12338Cell13 :
    0 ≤ cap12338 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12338 (parameters ⟨13,by decide⟩)
      (scalarRow12338.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12338 ⟨13,by decide⟩ ∧
    (scalarRow12338.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12338 ⟨13,by decide⟩ + (scalarRow12338.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12338.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12338.targetFrame := by
  norm_num [cap12338, scalarRow12338, sourceIndex, cell12338, BstLean.Part263.envelope, parameters]

theorem repair12338Cell14 :
    0 ≤ cap12338 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12338 (parameters ⟨14,by decide⟩)
      (scalarRow12338.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12338 ⟨14,by decide⟩ ∧
    (scalarRow12338.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12338 ⟨14,by decide⟩ + (scalarRow12338.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12338.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12338.targetFrame := by
  norm_num [cap12338, scalarRow12338, sourceIndex, cell12338, BstLean.Part263.envelope, parameters]

theorem repair12338Cell15 :
    0 ≤ cap12338 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12338 (parameters ⟨15,by decide⟩)
      (scalarRow12338.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12338 ⟨15,by decide⟩ ∧
    (scalarRow12338.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12338 ⟨15,by decide⟩ + (scalarRow12338.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12338.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12338.targetFrame := by
  norm_num [cap12338, scalarRow12338, sourceIndex, cell12338, BstLean.Part263.envelope, parameters]

theorem repair12338Cell16 :
    0 ≤ cap12338 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12338 (parameters ⟨16,by decide⟩)
      (scalarRow12338.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12338 ⟨16,by decide⟩ ∧
    (scalarRow12338.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12338 ⟨16,by decide⟩ + (scalarRow12338.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12338.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12338.targetFrame := by
  norm_num [cap12338, scalarRow12338, sourceIndex, cell12338, BstLean.Part263.envelope, parameters]

theorem repair12338Cell17 :
    0 ≤ cap12338 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12338 (parameters ⟨17,by decide⟩)
      (scalarRow12338.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12338 ⟨17,by decide⟩ ∧
    (scalarRow12338.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12338 ⟨17,by decide⟩ + (scalarRow12338.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12338.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12338.targetFrame := by
  norm_num [cap12338, scalarRow12338, sourceIndex, cell12338, BstLean.Part263.envelope, parameters]

theorem repair12338Cell18 :
    0 ≤ cap12338 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12338 (parameters ⟨18,by decide⟩)
      (scalarRow12338.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12338 ⟨18,by decide⟩ ∧
    (scalarRow12338.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12338 ⟨18,by decide⟩ + (scalarRow12338.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12338.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12338.targetFrame := by
  norm_num [cap12338, scalarRow12338, sourceIndex, cell12338, BstLean.Part263.envelope, parameters]

theorem repair12338Cell19 :
    0 ≤ cap12338 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12338 (parameters ⟨19,by decide⟩)
      (scalarRow12338.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12338 ⟨19,by decide⟩ ∧
    (scalarRow12338.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12338 ⟨19,by decide⟩ + (scalarRow12338.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12338.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12338.targetFrame := by
  norm_num [cap12338, scalarRow12338, sourceIndex, cell12338, BstLean.Part263.envelope, parameters]

theorem repair12338Cell20 :
    0 ≤ cap12338 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12338 (parameters ⟨20,by decide⟩)
      (scalarRow12338.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12338 ⟨20,by decide⟩ ∧
    (scalarRow12338.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12338 ⟨20,by decide⟩ + (scalarRow12338.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12338.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12338.targetFrame := by
  norm_num [cap12338, scalarRow12338, sourceIndex, cell12338, BstLean.Part263.envelope, parameters]

theorem repair12338Cell21 :
    0 ≤ cap12338 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12338 (parameters ⟨21,by decide⟩)
      (scalarRow12338.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12338 ⟨21,by decide⟩ ∧
    (scalarRow12338.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12338 ⟨21,by decide⟩ + (scalarRow12338.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12338.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12338.targetFrame := by
  norm_num [cap12338, scalarRow12338, sourceIndex, cell12338, BstLean.Part263.envelope, parameters]

theorem repair12338Cell22 :
    0 ≤ cap12338 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12338 (parameters ⟨22,by decide⟩)
      (scalarRow12338.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12338 ⟨22,by decide⟩ ∧
    (scalarRow12338.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12338 ⟨22,by decide⟩ + (scalarRow12338.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12338.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12338.targetFrame := by
  norm_num [cap12338, scalarRow12338, sourceIndex, cell12338, BstLean.Part263.envelope, parameters]

theorem repair12338Cell23 :
    0 ≤ cap12338 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12338 (parameters ⟨23,by decide⟩)
      (scalarRow12338.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12338 ⟨23,by decide⟩ ∧
    (scalarRow12338.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12338 ⟨23,by decide⟩ + (scalarRow12338.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12338.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12338.targetFrame := by
  norm_num [cap12338, scalarRow12338, sourceIndex, cell12338, BstLean.Part263.envelope, parameters]

theorem repair12338Cell24 :
    0 ≤ cap12338 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12338 (parameters ⟨24,by decide⟩)
      (scalarRow12338.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12338 ⟨24,by decide⟩ ∧
    (scalarRow12338.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12338 ⟨24,by decide⟩ + (scalarRow12338.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12338.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12338.targetFrame := by
  norm_num [cap12338, scalarRow12338, sourceIndex, cell12338, BstLean.Part263.envelope, parameters]

theorem repair12338Cell25 :
    0 ≤ cap12338 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12338 (parameters ⟨25,by decide⟩)
      (scalarRow12338.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12338 ⟨25,by decide⟩ ∧
    (scalarRow12338.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12338 ⟨25,by decide⟩ + (scalarRow12338.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12338.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12338.targetFrame := by
  norm_num [cap12338, scalarRow12338, sourceIndex, cell12338, BstLean.Part263.envelope, parameters]

theorem repair12338Cell26 :
    0 ≤ cap12338 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12338 (parameters ⟨26,by decide⟩)
      (scalarRow12338.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12338 ⟨26,by decide⟩ ∧
    (scalarRow12338.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12338 ⟨26,by decide⟩ + (scalarRow12338.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12338.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12338.targetFrame := by
  norm_num [cap12338, scalarRow12338, sourceIndex, cell12338, BstLean.Part263.envelope, parameters]

theorem repair12338Cell27 :
    0 ≤ cap12338 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12338 (parameters ⟨27,by decide⟩)
      (scalarRow12338.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12338 ⟨27,by decide⟩ ∧
    (scalarRow12338.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12338 ⟨27,by decide⟩ + (scalarRow12338.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12338.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12338.targetFrame := by
  norm_num [cap12338, scalarRow12338, sourceIndex, cell12338, BstLean.Part263.envelope, parameters]

theorem repair12338Cell28 :
    0 ≤ cap12338 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12338 (parameters ⟨28,by decide⟩)
      (scalarRow12338.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12338 ⟨28,by decide⟩ ∧
    (scalarRow12338.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12338 ⟨28,by decide⟩ + (scalarRow12338.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12338.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12338.targetFrame := by
  norm_num [cap12338, scalarRow12338, sourceIndex, cell12338, BstLean.Part263.envelope, parameters]

theorem repair12338Cell29 :
    0 ≤ cap12338 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12338 (parameters ⟨29,by decide⟩)
      (scalarRow12338.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12338 ⟨29,by decide⟩ ∧
    (scalarRow12338.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12338 ⟨29,by decide⟩ + (scalarRow12338.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12338.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12338.targetFrame := by
  norm_num [cap12338, scalarRow12338, sourceIndex, cell12338, BstLean.Part263.envelope, parameters]

theorem repair12338Cell30 :
    0 ≤ cap12338 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12338 (parameters ⟨30,by decide⟩)
      (scalarRow12338.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12338 ⟨30,by decide⟩ ∧
    (scalarRow12338.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12338 ⟨30,by decide⟩ + (scalarRow12338.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12338.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12338.targetFrame := by
  norm_num [cap12338, scalarRow12338, sourceIndex, cell12338, BstLean.Part263.envelope, parameters]

theorem repair12338Cell31 :
    0 ≤ cap12338 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12338 (parameters ⟨31,by decide⟩)
      (scalarRow12338.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12338 ⟨31,by decide⟩ ∧
    (scalarRow12338.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12338 ⟨31,by decide⟩ + (scalarRow12338.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12338.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12338.targetFrame := by
  norm_num [cap12338, scalarRow12338, sourceIndex, cell12338, BstLean.Part263.envelope, parameters]

theorem repair12338Cell32 :
    0 ≤ cap12338 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12338 (parameters ⟨32,by decide⟩)
      (scalarRow12338.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12338 ⟨32,by decide⟩ ∧
    (scalarRow12338.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12338 ⟨32,by decide⟩ + (scalarRow12338.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12338.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12338.targetFrame := by
  norm_num [cap12338, scalarRow12338, sourceIndex, cell12338, BstLean.Part263.envelope, parameters]

theorem repair12338Cell33 :
    0 ≤ cap12338 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12338 (parameters ⟨33,by decide⟩)
      (scalarRow12338.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12338 ⟨33,by decide⟩ ∧
    (scalarRow12338.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12338 ⟨33,by decide⟩ + (scalarRow12338.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12338.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12338.targetFrame := by
  norm_num [cap12338, scalarRow12338, sourceIndex, cell12338, BstLean.Part263.envelope, parameters]

theorem repair12338Cell34 :
    0 ≤ cap12338 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12338 (parameters ⟨34,by decide⟩)
      (scalarRow12338.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12338 ⟨34,by decide⟩ ∧
    (scalarRow12338.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12338 ⟨34,by decide⟩ + (scalarRow12338.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12338.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12338.targetFrame := by
  norm_num [cap12338, scalarRow12338, sourceIndex, cell12338, BstLean.Part263.envelope, parameters]

theorem repair12338Cell35 :
    0 ≤ cap12338 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12338 (parameters ⟨35,by decide⟩)
      (scalarRow12338.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12338 ⟨35,by decide⟩ ∧
    (scalarRow12338.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12338 ⟨35,by decide⟩ + (scalarRow12338.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12338.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12338.targetFrame := by
  norm_num [cap12338, scalarRow12338, sourceIndex, cell12338, BstLean.Part263.envelope, parameters]

theorem repair12338Cell36 :
    0 ≤ cap12338 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12338 (parameters ⟨36,by decide⟩)
      (scalarRow12338.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12338 ⟨36,by decide⟩ ∧
    (scalarRow12338.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12338 ⟨36,by decide⟩ + (scalarRow12338.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12338.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12338.targetFrame := by
  norm_num [cap12338, scalarRow12338, sourceIndex, cell12338, BstLean.Part263.envelope, parameters]

theorem repair12338Cell37 :
    0 ≤ cap12338 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12338 (parameters ⟨37,by decide⟩)
      (scalarRow12338.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12338 ⟨37,by decide⟩ ∧
    (scalarRow12338.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12338 ⟨37,by decide⟩ + (scalarRow12338.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12338.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12338.targetFrame := by
  norm_num [cap12338, scalarRow12338, sourceIndex, cell12338, BstLean.Part263.envelope, parameters]

theorem repair12338Cell38 :
    0 ≤ cap12338 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12338 (parameters ⟨38,by decide⟩)
      (scalarRow12338.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12338 ⟨38,by decide⟩ ∧
    (scalarRow12338.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12338 ⟨38,by decide⟩ + (scalarRow12338.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12338.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12338.targetFrame := by
  norm_num [cap12338, scalarRow12338, sourceIndex, cell12338, BstLean.Part263.envelope, parameters]

theorem repair12338Cell39 :
    0 ≤ cap12338 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12338 (parameters ⟨39,by decide⟩)
      (scalarRow12338.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12338 ⟨39,by decide⟩ ∧
    (scalarRow12338.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12338 ⟨39,by decide⟩ + (scalarRow12338.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12338.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12338.targetFrame := by
  norm_num [cap12338, scalarRow12338, sourceIndex, cell12338, BstLean.Part263.envelope, parameters]

theorem repair12338Cell40 :
    0 ≤ cap12338 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12338 (parameters ⟨40,by decide⟩)
      (scalarRow12338.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12338 ⟨40,by decide⟩ ∧
    (scalarRow12338.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12338 ⟨40,by decide⟩ + (scalarRow12338.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12338.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12338.targetFrame := by
  norm_num [cap12338, scalarRow12338, sourceIndex, cell12338, BstLean.Part263.envelope, parameters]

theorem repair12338Cell41 :
    0 ≤ cap12338 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12338 (parameters ⟨41,by decide⟩)
      (scalarRow12338.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12338 ⟨41,by decide⟩ ∧
    (scalarRow12338.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12338 ⟨41,by decide⟩ + (scalarRow12338.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12338.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12338.targetFrame := by
  norm_num [cap12338, scalarRow12338, sourceIndex, cell12338, BstLean.Part263.envelope, parameters]

theorem repair12338Cell42 :
    0 ≤ cap12338 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12338 (parameters ⟨42,by decide⟩)
      (scalarRow12338.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12338 ⟨42,by decide⟩ ∧
    (scalarRow12338.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12338 ⟨42,by decide⟩ + (scalarRow12338.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12338.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12338.targetFrame := by
  norm_num [cap12338, scalarRow12338, sourceIndex, cell12338, BstLean.Part263.envelope, parameters]

theorem repair12338Cells (j : Fin 43) :
    0 ≤ cap12338 j ∧
    BstLean.Part263.envelope 12338 (parameters j) (scalarRow12338.table (sourceIndex j)).upper ≤ cap12338 j ∧
    (scalarRow12338.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12338 j + (scalarRow12338.table (sourceIndex j)).centre) /
      (scalarRow12338.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12338.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12338Cell0
  | ⟨1,_⟩ => exact repair12338Cell1
  | ⟨2,_⟩ => exact repair12338Cell2
  | ⟨3,_⟩ => exact repair12338Cell3
  | ⟨4,_⟩ => exact repair12338Cell4
  | ⟨5,_⟩ => exact repair12338Cell5
  | ⟨6,_⟩ => exact repair12338Cell6
  | ⟨7,_⟩ => exact repair12338Cell7
  | ⟨8,_⟩ => exact repair12338Cell8
  | ⟨9,_⟩ => exact repair12338Cell9
  | ⟨10,_⟩ => exact repair12338Cell10
  | ⟨11,_⟩ => exact repair12338Cell11
  | ⟨12,_⟩ => exact repair12338Cell12
  | ⟨13,_⟩ => exact repair12338Cell13
  | ⟨14,_⟩ => exact repair12338Cell14
  | ⟨15,_⟩ => exact repair12338Cell15
  | ⟨16,_⟩ => exact repair12338Cell16
  | ⟨17,_⟩ => exact repair12338Cell17
  | ⟨18,_⟩ => exact repair12338Cell18
  | ⟨19,_⟩ => exact repair12338Cell19
  | ⟨20,_⟩ => exact repair12338Cell20
  | ⟨21,_⟩ => exact repair12338Cell21
  | ⟨22,_⟩ => exact repair12338Cell22
  | ⟨23,_⟩ => exact repair12338Cell23
  | ⟨24,_⟩ => exact repair12338Cell24
  | ⟨25,_⟩ => exact repair12338Cell25
  | ⟨26,_⟩ => exact repair12338Cell26
  | ⟨27,_⟩ => exact repair12338Cell27
  | ⟨28,_⟩ => exact repair12338Cell28
  | ⟨29,_⟩ => exact repair12338Cell29
  | ⟨30,_⟩ => exact repair12338Cell30
  | ⟨31,_⟩ => exact repair12338Cell31
  | ⟨32,_⟩ => exact repair12338Cell32
  | ⟨33,_⟩ => exact repair12338Cell33
  | ⟨34,_⟩ => exact repair12338Cell34
  | ⟨35,_⟩ => exact repair12338Cell35
  | ⟨36,_⟩ => exact repair12338Cell36
  | ⟨37,_⟩ => exact repair12338Cell37
  | ⟨38,_⟩ => exact repair12338Cell38
  | ⟨39,_⟩ => exact repair12338Cell39
  | ⟨40,_⟩ => exact repair12338Cell40
  | ⟨41,_⟩ => exact repair12338Cell41
  | ⟨42,_⟩ => exact repair12338Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12338 : FrameRepair 12338 scalarRow12338 where
  cap := cap12338
  cap_nonneg := fun j => (repair12338Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12338])
  endpoint := fun j => (repair12338Cells j).2.1
  endpoint_upper := fun j => (repair12338Cells j).2.2.1
  frame := fun j => (repair12338Cells j).2.2.2

noncomputable def cap12339 : Fin 43 → ℝ
  | ⟨0,_⟩ => (275944127 / 1000000000 : ℝ)
  | ⟨1,_⟩ => (13817333 / 50000000 : ℝ)
  | ⟨2,_⟩ => (276748199 / 1000000000 : ℝ)
  | ⟨3,_⟩ => (138574371 / 500000000 : ℝ)
  | ⟨4,_⟩ => (55509659 / 200000000 : ℝ)
  | ⟨5,_⟩ => (277946859 / 1000000000 : ℝ)
  | ⟨6,_⟩ => (139171981 / 500000000 : ℝ)
  | ⟨7,_⟩ => (278740561 / 1000000000 : ℝ)
  | ⟨8,_⟩ => (34892023 / 125000000 : ℝ)
  | ⟨9,_⟩ => (55906167 / 200000000 : ℝ)
  | ⟨10,_⟩ => (69981129 / 250000000 : ℝ)
  | ⟨11,_⟩ => (280316749 / 1000000000 : ℝ)
  | ⟨12,_⟩ => (140354253 / 500000000 : ℝ)
  | ⟨13,_⟩ => (4392169 / 15625000 : ℝ)
  | ⟨14,_⟩ => (281489059 / 1000000000 : ℝ)
  | ⟨15,_⟩ => (70469551 / 250000000 : ℝ)
  | ⟨16,_⟩ => (141133203 / 500000000 : ℝ)
  | ⟨17,_⟩ => (141326839 / 500000000 : ℝ)
  | ⟨18,_⟩ => (283040011 / 1000000000 : ℝ)
  | ⟨19,_⟩ => (35428177 / 125000000 : ℝ)
  | ⟨20,_⟩ => (141904947 / 500000000 : ℝ)
  | ⟨21,_⟩ => (284193457 / 1000000000 : ℝ)
  | ⟨22,_⟩ => (284576097 / 1000000000 : ℝ)
  | ⟨23,_⟩ => (142478663 / 500000000 : ℝ)
  | ⟨24,_⟩ => (285338143 / 1000000000 : ℝ)
  | ⟨25,_⟩ => (357147 / 1250000 : ℝ)
  | ⟨26,_⟩ => (286096653 / 1000000000 : ℝ)
  | ⟨27,_⟩ => (71618577 / 250000000 : ℝ)
  | ⟨28,_⟩ => (143425533 / 500000000 : ℝ)
  | ⟨29,_⟩ => (287226929 / 1000000000 : ℝ)
  | ⟨30,_⟩ => (1438007 / 5000000 : ℝ)
  | ⟨31,_⟩ => (143987743 / 500000000 : ℝ)
  | ⟨32,_⟩ => (288348693 / 1000000000 : ℝ)
  | ⟨33,_⟩ => (288720509 / 1000000000 : ℝ)
  | ⟨34,_⟩ => (72272863 / 250000000 : ℝ)
  | ⟨35,_⟩ => (289461523 / 1000000000 : ℝ)
  | ⟨36,_⟩ => (144915359 / 500000000 : ℝ)
  | ⟨37,_⟩ => (145099527 / 500000000 : ℝ)
  | ⟨38,_⟩ => (145283263 / 500000000 : ℝ)
  | ⟨39,_⟩ => (145466313 / 500000000 : ℝ)
  | ⟨40,_⟩ => (72824467 / 250000000 : ℝ)
  | ⟨41,_⟩ => (145831129 / 500000000 : ℝ)
  | ⟨42,_⟩ => (146012899 / 500000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12339Cell0 :
    0 ≤ cap12339 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12339 (parameters ⟨0,by decide⟩)
      (scalarRow12339.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12339 ⟨0,by decide⟩ ∧
    (scalarRow12339.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12339 ⟨0,by decide⟩ + (scalarRow12339.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12339.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12339.targetFrame := by
  norm_num [cap12339, scalarRow12339, sourceIndex, cell12339, BstLean.Part263.envelope, parameters]

theorem repair12339Cell1 :
    0 ≤ cap12339 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12339 (parameters ⟨1,by decide⟩)
      (scalarRow12339.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12339 ⟨1,by decide⟩ ∧
    (scalarRow12339.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12339 ⟨1,by decide⟩ + (scalarRow12339.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12339.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12339.targetFrame := by
  norm_num [cap12339, scalarRow12339, sourceIndex, cell12339, BstLean.Part263.envelope, parameters]

theorem repair12339Cell2 :
    0 ≤ cap12339 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12339 (parameters ⟨2,by decide⟩)
      (scalarRow12339.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12339 ⟨2,by decide⟩ ∧
    (scalarRow12339.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12339 ⟨2,by decide⟩ + (scalarRow12339.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12339.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12339.targetFrame := by
  norm_num [cap12339, scalarRow12339, sourceIndex, cell12339, BstLean.Part263.envelope, parameters]

theorem repair12339Cell3 :
    0 ≤ cap12339 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12339 (parameters ⟨3,by decide⟩)
      (scalarRow12339.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12339 ⟨3,by decide⟩ ∧
    (scalarRow12339.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12339 ⟨3,by decide⟩ + (scalarRow12339.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12339.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12339.targetFrame := by
  norm_num [cap12339, scalarRow12339, sourceIndex, cell12339, BstLean.Part263.envelope, parameters]

theorem repair12339Cell4 :
    0 ≤ cap12339 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12339 (parameters ⟨4,by decide⟩)
      (scalarRow12339.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12339 ⟨4,by decide⟩ ∧
    (scalarRow12339.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12339 ⟨4,by decide⟩ + (scalarRow12339.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12339.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12339.targetFrame := by
  norm_num [cap12339, scalarRow12339, sourceIndex, cell12339, BstLean.Part263.envelope, parameters]

theorem repair12339Cell5 :
    0 ≤ cap12339 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12339 (parameters ⟨5,by decide⟩)
      (scalarRow12339.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12339 ⟨5,by decide⟩ ∧
    (scalarRow12339.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12339 ⟨5,by decide⟩ + (scalarRow12339.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12339.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12339.targetFrame := by
  norm_num [cap12339, scalarRow12339, sourceIndex, cell12339, BstLean.Part263.envelope, parameters]

theorem repair12339Cell6 :
    0 ≤ cap12339 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12339 (parameters ⟨6,by decide⟩)
      (scalarRow12339.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12339 ⟨6,by decide⟩ ∧
    (scalarRow12339.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12339 ⟨6,by decide⟩ + (scalarRow12339.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12339.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12339.targetFrame := by
  norm_num [cap12339, scalarRow12339, sourceIndex, cell12339, BstLean.Part263.envelope, parameters]

theorem repair12339Cell7 :
    0 ≤ cap12339 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12339 (parameters ⟨7,by decide⟩)
      (scalarRow12339.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12339 ⟨7,by decide⟩ ∧
    (scalarRow12339.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12339 ⟨7,by decide⟩ + (scalarRow12339.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12339.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12339.targetFrame := by
  norm_num [cap12339, scalarRow12339, sourceIndex, cell12339, BstLean.Part263.envelope, parameters]

theorem repair12339Cell8 :
    0 ≤ cap12339 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12339 (parameters ⟨8,by decide⟩)
      (scalarRow12339.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12339 ⟨8,by decide⟩ ∧
    (scalarRow12339.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12339 ⟨8,by decide⟩ + (scalarRow12339.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12339.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12339.targetFrame := by
  norm_num [cap12339, scalarRow12339, sourceIndex, cell12339, BstLean.Part263.envelope, parameters]

theorem repair12339Cell9 :
    0 ≤ cap12339 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12339 (parameters ⟨9,by decide⟩)
      (scalarRow12339.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12339 ⟨9,by decide⟩ ∧
    (scalarRow12339.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12339 ⟨9,by decide⟩ + (scalarRow12339.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12339.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12339.targetFrame := by
  norm_num [cap12339, scalarRow12339, sourceIndex, cell12339, BstLean.Part263.envelope, parameters]

theorem repair12339Cell10 :
    0 ≤ cap12339 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12339 (parameters ⟨10,by decide⟩)
      (scalarRow12339.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12339 ⟨10,by decide⟩ ∧
    (scalarRow12339.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12339 ⟨10,by decide⟩ + (scalarRow12339.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12339.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12339.targetFrame := by
  norm_num [cap12339, scalarRow12339, sourceIndex, cell12339, BstLean.Part263.envelope, parameters]

theorem repair12339Cell11 :
    0 ≤ cap12339 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12339 (parameters ⟨11,by decide⟩)
      (scalarRow12339.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12339 ⟨11,by decide⟩ ∧
    (scalarRow12339.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12339 ⟨11,by decide⟩ + (scalarRow12339.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12339.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12339.targetFrame := by
  norm_num [cap12339, scalarRow12339, sourceIndex, cell12339, BstLean.Part263.envelope, parameters]

theorem repair12339Cell12 :
    0 ≤ cap12339 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12339 (parameters ⟨12,by decide⟩)
      (scalarRow12339.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12339 ⟨12,by decide⟩ ∧
    (scalarRow12339.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12339 ⟨12,by decide⟩ + (scalarRow12339.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12339.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12339.targetFrame := by
  norm_num [cap12339, scalarRow12339, sourceIndex, cell12339, BstLean.Part263.envelope, parameters]

theorem repair12339Cell13 :
    0 ≤ cap12339 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12339 (parameters ⟨13,by decide⟩)
      (scalarRow12339.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12339 ⟨13,by decide⟩ ∧
    (scalarRow12339.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12339 ⟨13,by decide⟩ + (scalarRow12339.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12339.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12339.targetFrame := by
  norm_num [cap12339, scalarRow12339, sourceIndex, cell12339, BstLean.Part263.envelope, parameters]

theorem repair12339Cell14 :
    0 ≤ cap12339 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12339 (parameters ⟨14,by decide⟩)
      (scalarRow12339.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12339 ⟨14,by decide⟩ ∧
    (scalarRow12339.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12339 ⟨14,by decide⟩ + (scalarRow12339.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12339.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12339.targetFrame := by
  norm_num [cap12339, scalarRow12339, sourceIndex, cell12339, BstLean.Part263.envelope, parameters]

theorem repair12339Cell15 :
    0 ≤ cap12339 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12339 (parameters ⟨15,by decide⟩)
      (scalarRow12339.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12339 ⟨15,by decide⟩ ∧
    (scalarRow12339.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12339 ⟨15,by decide⟩ + (scalarRow12339.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12339.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12339.targetFrame := by
  norm_num [cap12339, scalarRow12339, sourceIndex, cell12339, BstLean.Part263.envelope, parameters]

theorem repair12339Cell16 :
    0 ≤ cap12339 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12339 (parameters ⟨16,by decide⟩)
      (scalarRow12339.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12339 ⟨16,by decide⟩ ∧
    (scalarRow12339.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12339 ⟨16,by decide⟩ + (scalarRow12339.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12339.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12339.targetFrame := by
  norm_num [cap12339, scalarRow12339, sourceIndex, cell12339, BstLean.Part263.envelope, parameters]

theorem repair12339Cell17 :
    0 ≤ cap12339 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12339 (parameters ⟨17,by decide⟩)
      (scalarRow12339.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12339 ⟨17,by decide⟩ ∧
    (scalarRow12339.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12339 ⟨17,by decide⟩ + (scalarRow12339.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12339.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12339.targetFrame := by
  norm_num [cap12339, scalarRow12339, sourceIndex, cell12339, BstLean.Part263.envelope, parameters]

theorem repair12339Cell18 :
    0 ≤ cap12339 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12339 (parameters ⟨18,by decide⟩)
      (scalarRow12339.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12339 ⟨18,by decide⟩ ∧
    (scalarRow12339.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12339 ⟨18,by decide⟩ + (scalarRow12339.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12339.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12339.targetFrame := by
  norm_num [cap12339, scalarRow12339, sourceIndex, cell12339, BstLean.Part263.envelope, parameters]

theorem repair12339Cell19 :
    0 ≤ cap12339 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12339 (parameters ⟨19,by decide⟩)
      (scalarRow12339.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12339 ⟨19,by decide⟩ ∧
    (scalarRow12339.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12339 ⟨19,by decide⟩ + (scalarRow12339.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12339.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12339.targetFrame := by
  norm_num [cap12339, scalarRow12339, sourceIndex, cell12339, BstLean.Part263.envelope, parameters]

theorem repair12339Cell20 :
    0 ≤ cap12339 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12339 (parameters ⟨20,by decide⟩)
      (scalarRow12339.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12339 ⟨20,by decide⟩ ∧
    (scalarRow12339.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12339 ⟨20,by decide⟩ + (scalarRow12339.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12339.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12339.targetFrame := by
  norm_num [cap12339, scalarRow12339, sourceIndex, cell12339, BstLean.Part263.envelope, parameters]

theorem repair12339Cell21 :
    0 ≤ cap12339 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12339 (parameters ⟨21,by decide⟩)
      (scalarRow12339.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12339 ⟨21,by decide⟩ ∧
    (scalarRow12339.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12339 ⟨21,by decide⟩ + (scalarRow12339.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12339.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12339.targetFrame := by
  norm_num [cap12339, scalarRow12339, sourceIndex, cell12339, BstLean.Part263.envelope, parameters]

theorem repair12339Cell22 :
    0 ≤ cap12339 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12339 (parameters ⟨22,by decide⟩)
      (scalarRow12339.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12339 ⟨22,by decide⟩ ∧
    (scalarRow12339.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12339 ⟨22,by decide⟩ + (scalarRow12339.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12339.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12339.targetFrame := by
  norm_num [cap12339, scalarRow12339, sourceIndex, cell12339, BstLean.Part263.envelope, parameters]

theorem repair12339Cell23 :
    0 ≤ cap12339 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12339 (parameters ⟨23,by decide⟩)
      (scalarRow12339.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12339 ⟨23,by decide⟩ ∧
    (scalarRow12339.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12339 ⟨23,by decide⟩ + (scalarRow12339.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12339.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12339.targetFrame := by
  norm_num [cap12339, scalarRow12339, sourceIndex, cell12339, BstLean.Part263.envelope, parameters]

theorem repair12339Cell24 :
    0 ≤ cap12339 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12339 (parameters ⟨24,by decide⟩)
      (scalarRow12339.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12339 ⟨24,by decide⟩ ∧
    (scalarRow12339.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12339 ⟨24,by decide⟩ + (scalarRow12339.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12339.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12339.targetFrame := by
  norm_num [cap12339, scalarRow12339, sourceIndex, cell12339, BstLean.Part263.envelope, parameters]

theorem repair12339Cell25 :
    0 ≤ cap12339 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12339 (parameters ⟨25,by decide⟩)
      (scalarRow12339.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12339 ⟨25,by decide⟩ ∧
    (scalarRow12339.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12339 ⟨25,by decide⟩ + (scalarRow12339.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12339.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12339.targetFrame := by
  norm_num [cap12339, scalarRow12339, sourceIndex, cell12339, BstLean.Part263.envelope, parameters]

theorem repair12339Cell26 :
    0 ≤ cap12339 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12339 (parameters ⟨26,by decide⟩)
      (scalarRow12339.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12339 ⟨26,by decide⟩ ∧
    (scalarRow12339.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12339 ⟨26,by decide⟩ + (scalarRow12339.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12339.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12339.targetFrame := by
  norm_num [cap12339, scalarRow12339, sourceIndex, cell12339, BstLean.Part263.envelope, parameters]

theorem repair12339Cell27 :
    0 ≤ cap12339 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12339 (parameters ⟨27,by decide⟩)
      (scalarRow12339.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12339 ⟨27,by decide⟩ ∧
    (scalarRow12339.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12339 ⟨27,by decide⟩ + (scalarRow12339.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12339.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12339.targetFrame := by
  norm_num [cap12339, scalarRow12339, sourceIndex, cell12339, BstLean.Part263.envelope, parameters]

theorem repair12339Cell28 :
    0 ≤ cap12339 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12339 (parameters ⟨28,by decide⟩)
      (scalarRow12339.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12339 ⟨28,by decide⟩ ∧
    (scalarRow12339.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12339 ⟨28,by decide⟩ + (scalarRow12339.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12339.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12339.targetFrame := by
  norm_num [cap12339, scalarRow12339, sourceIndex, cell12339, BstLean.Part263.envelope, parameters]

theorem repair12339Cell29 :
    0 ≤ cap12339 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12339 (parameters ⟨29,by decide⟩)
      (scalarRow12339.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12339 ⟨29,by decide⟩ ∧
    (scalarRow12339.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12339 ⟨29,by decide⟩ + (scalarRow12339.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12339.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12339.targetFrame := by
  norm_num [cap12339, scalarRow12339, sourceIndex, cell12339, BstLean.Part263.envelope, parameters]

theorem repair12339Cell30 :
    0 ≤ cap12339 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12339 (parameters ⟨30,by decide⟩)
      (scalarRow12339.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12339 ⟨30,by decide⟩ ∧
    (scalarRow12339.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12339 ⟨30,by decide⟩ + (scalarRow12339.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12339.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12339.targetFrame := by
  norm_num [cap12339, scalarRow12339, sourceIndex, cell12339, BstLean.Part263.envelope, parameters]

theorem repair12339Cell31 :
    0 ≤ cap12339 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12339 (parameters ⟨31,by decide⟩)
      (scalarRow12339.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12339 ⟨31,by decide⟩ ∧
    (scalarRow12339.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12339 ⟨31,by decide⟩ + (scalarRow12339.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12339.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12339.targetFrame := by
  norm_num [cap12339, scalarRow12339, sourceIndex, cell12339, BstLean.Part263.envelope, parameters]

theorem repair12339Cell32 :
    0 ≤ cap12339 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12339 (parameters ⟨32,by decide⟩)
      (scalarRow12339.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12339 ⟨32,by decide⟩ ∧
    (scalarRow12339.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12339 ⟨32,by decide⟩ + (scalarRow12339.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12339.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12339.targetFrame := by
  norm_num [cap12339, scalarRow12339, sourceIndex, cell12339, BstLean.Part263.envelope, parameters]

theorem repair12339Cell33 :
    0 ≤ cap12339 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12339 (parameters ⟨33,by decide⟩)
      (scalarRow12339.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12339 ⟨33,by decide⟩ ∧
    (scalarRow12339.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12339 ⟨33,by decide⟩ + (scalarRow12339.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12339.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12339.targetFrame := by
  norm_num [cap12339, scalarRow12339, sourceIndex, cell12339, BstLean.Part263.envelope, parameters]

theorem repair12339Cell34 :
    0 ≤ cap12339 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12339 (parameters ⟨34,by decide⟩)
      (scalarRow12339.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12339 ⟨34,by decide⟩ ∧
    (scalarRow12339.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12339 ⟨34,by decide⟩ + (scalarRow12339.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12339.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12339.targetFrame := by
  norm_num [cap12339, scalarRow12339, sourceIndex, cell12339, BstLean.Part263.envelope, parameters]

theorem repair12339Cell35 :
    0 ≤ cap12339 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12339 (parameters ⟨35,by decide⟩)
      (scalarRow12339.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12339 ⟨35,by decide⟩ ∧
    (scalarRow12339.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12339 ⟨35,by decide⟩ + (scalarRow12339.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12339.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12339.targetFrame := by
  norm_num [cap12339, scalarRow12339, sourceIndex, cell12339, BstLean.Part263.envelope, parameters]

theorem repair12339Cell36 :
    0 ≤ cap12339 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12339 (parameters ⟨36,by decide⟩)
      (scalarRow12339.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12339 ⟨36,by decide⟩ ∧
    (scalarRow12339.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12339 ⟨36,by decide⟩ + (scalarRow12339.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12339.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12339.targetFrame := by
  norm_num [cap12339, scalarRow12339, sourceIndex, cell12339, BstLean.Part263.envelope, parameters]

theorem repair12339Cell37 :
    0 ≤ cap12339 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12339 (parameters ⟨37,by decide⟩)
      (scalarRow12339.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12339 ⟨37,by decide⟩ ∧
    (scalarRow12339.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12339 ⟨37,by decide⟩ + (scalarRow12339.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12339.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12339.targetFrame := by
  norm_num [cap12339, scalarRow12339, sourceIndex, cell12339, BstLean.Part263.envelope, parameters]

theorem repair12339Cell38 :
    0 ≤ cap12339 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12339 (parameters ⟨38,by decide⟩)
      (scalarRow12339.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12339 ⟨38,by decide⟩ ∧
    (scalarRow12339.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12339 ⟨38,by decide⟩ + (scalarRow12339.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12339.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12339.targetFrame := by
  norm_num [cap12339, scalarRow12339, sourceIndex, cell12339, BstLean.Part263.envelope, parameters]

theorem repair12339Cell39 :
    0 ≤ cap12339 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12339 (parameters ⟨39,by decide⟩)
      (scalarRow12339.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12339 ⟨39,by decide⟩ ∧
    (scalarRow12339.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12339 ⟨39,by decide⟩ + (scalarRow12339.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12339.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12339.targetFrame := by
  norm_num [cap12339, scalarRow12339, sourceIndex, cell12339, BstLean.Part263.envelope, parameters]

theorem repair12339Cell40 :
    0 ≤ cap12339 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12339 (parameters ⟨40,by decide⟩)
      (scalarRow12339.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12339 ⟨40,by decide⟩ ∧
    (scalarRow12339.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12339 ⟨40,by decide⟩ + (scalarRow12339.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12339.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12339.targetFrame := by
  norm_num [cap12339, scalarRow12339, sourceIndex, cell12339, BstLean.Part263.envelope, parameters]

theorem repair12339Cell41 :
    0 ≤ cap12339 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12339 (parameters ⟨41,by decide⟩)
      (scalarRow12339.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12339 ⟨41,by decide⟩ ∧
    (scalarRow12339.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12339 ⟨41,by decide⟩ + (scalarRow12339.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12339.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12339.targetFrame := by
  norm_num [cap12339, scalarRow12339, sourceIndex, cell12339, BstLean.Part263.envelope, parameters]

theorem repair12339Cell42 :
    0 ≤ cap12339 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12339 (parameters ⟨42,by decide⟩)
      (scalarRow12339.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12339 ⟨42,by decide⟩ ∧
    (scalarRow12339.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12339 ⟨42,by decide⟩ + (scalarRow12339.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12339.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12339.targetFrame := by
  norm_num [cap12339, scalarRow12339, sourceIndex, cell12339, BstLean.Part263.envelope, parameters]

theorem repair12339Cells (j : Fin 43) :
    0 ≤ cap12339 j ∧
    BstLean.Part263.envelope 12339 (parameters j) (scalarRow12339.table (sourceIndex j)).upper ≤ cap12339 j ∧
    (scalarRow12339.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12339 j + (scalarRow12339.table (sourceIndex j)).centre) /
      (scalarRow12339.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12339.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12339Cell0
  | ⟨1,_⟩ => exact repair12339Cell1
  | ⟨2,_⟩ => exact repair12339Cell2
  | ⟨3,_⟩ => exact repair12339Cell3
  | ⟨4,_⟩ => exact repair12339Cell4
  | ⟨5,_⟩ => exact repair12339Cell5
  | ⟨6,_⟩ => exact repair12339Cell6
  | ⟨7,_⟩ => exact repair12339Cell7
  | ⟨8,_⟩ => exact repair12339Cell8
  | ⟨9,_⟩ => exact repair12339Cell9
  | ⟨10,_⟩ => exact repair12339Cell10
  | ⟨11,_⟩ => exact repair12339Cell11
  | ⟨12,_⟩ => exact repair12339Cell12
  | ⟨13,_⟩ => exact repair12339Cell13
  | ⟨14,_⟩ => exact repair12339Cell14
  | ⟨15,_⟩ => exact repair12339Cell15
  | ⟨16,_⟩ => exact repair12339Cell16
  | ⟨17,_⟩ => exact repair12339Cell17
  | ⟨18,_⟩ => exact repair12339Cell18
  | ⟨19,_⟩ => exact repair12339Cell19
  | ⟨20,_⟩ => exact repair12339Cell20
  | ⟨21,_⟩ => exact repair12339Cell21
  | ⟨22,_⟩ => exact repair12339Cell22
  | ⟨23,_⟩ => exact repair12339Cell23
  | ⟨24,_⟩ => exact repair12339Cell24
  | ⟨25,_⟩ => exact repair12339Cell25
  | ⟨26,_⟩ => exact repair12339Cell26
  | ⟨27,_⟩ => exact repair12339Cell27
  | ⟨28,_⟩ => exact repair12339Cell28
  | ⟨29,_⟩ => exact repair12339Cell29
  | ⟨30,_⟩ => exact repair12339Cell30
  | ⟨31,_⟩ => exact repair12339Cell31
  | ⟨32,_⟩ => exact repair12339Cell32
  | ⟨33,_⟩ => exact repair12339Cell33
  | ⟨34,_⟩ => exact repair12339Cell34
  | ⟨35,_⟩ => exact repair12339Cell35
  | ⟨36,_⟩ => exact repair12339Cell36
  | ⟨37,_⟩ => exact repair12339Cell37
  | ⟨38,_⟩ => exact repair12339Cell38
  | ⟨39,_⟩ => exact repair12339Cell39
  | ⟨40,_⟩ => exact repair12339Cell40
  | ⟨41,_⟩ => exact repair12339Cell41
  | ⟨42,_⟩ => exact repair12339Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12339 : FrameRepair 12339 scalarRow12339 where
  cap := cap12339
  cap_nonneg := fun j => (repair12339Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12339])
  endpoint := fun j => (repair12339Cells j).2.1
  endpoint_upper := fun j => (repair12339Cells j).2.2.1
  frame := fun j => (repair12339Cells j).2.2.2

noncomputable def cap12340 : Fin 43 → ℝ
  | ⟨0,_⟩ => (68986013 / 250000000 : ℝ)
  | ⟨1,_⟩ => (138173289 / 500000000 : ℝ)
  | ⟨2,_⟩ => (17296757 / 62500000 : ℝ)
  | ⟨3,_⟩ => (34643581 / 125000000 : ℝ)
  | ⟨4,_⟩ => (138774097 / 500000000 : ℝ)
  | ⟨5,_⟩ => (2171459 / 7812500 : ℝ)
  | ⟨6,_⟩ => (278343849 / 1000000000 : ℝ)
  | ⟨7,_⟩ => (278740441 / 1000000000 : ℝ)
  | ⟨8,_⟩ => (279136057 / 1000000000 : ℝ)
  | ⟨9,_⟩ => (139765351 / 500000000 : ℝ)
  | ⟨10,_⟩ => (279924377 / 1000000000 : ℝ)
  | ⟨11,_⟩ => (70079151 / 250000000 : ℝ)
  | ⟨12,_⟩ => (140354177 / 500000000 : ℝ)
  | ⟨13,_⟩ => (140549329 / 500000000 : ℝ)
  | ⟨14,_⟩ => (56297779 / 200000000 : ℝ)
  | ⟨15,_⟩ => (140939017 / 500000000 : ℝ)
  | ⟨16,_⟩ => (28226623 / 100000000 : ℝ)
  | ⟨17,_⟩ => (56530699 / 200000000 : ℝ)
  | ⟨18,_⟩ => (141519911 / 500000000 : ℝ)
  | ⟨19,_⟩ => (283425221 / 1000000000 : ℝ)
  | ⟨20,_⟩ => (283809693 / 1000000000 : ℝ)
  | ⟨21,_⟩ => (1136773 / 4000000 : ℝ)
  | ⟨22,_⟩ => (284575883 / 1000000000 : ℝ)
  | ⟨23,_⟩ => (284957107 / 1000000000 : ℝ)
  | ⟨24,_⟩ => (142668959 / 500000000 : ℝ)
  | ⟨25,_⟩ => (285717369 / 1000000000 : ℝ)
  | ⟨26,_⟩ => (57219283 / 200000000 : ℝ)
  | ⟨27,_⟩ => (17904629 / 62500000 : ℝ)
  | ⟨28,_⟩ => (1120511 / 3906250 : ℝ)
  | ⟨29,_⟩ => (287226673 / 1000000000 : ℝ)
  | ⟨30,_⟩ => (287601137 / 1000000000 : ℝ)
  | ⟨31,_⟩ => (143987609 / 500000000 : ℝ)
  | ⟨32,_⟩ => (144174209 / 500000000 : ℝ)
  | ⟨33,_⟩ => (288720229 / 1000000000 : ℝ)
  | ⟨34,_⟩ => (57818233 / 200000000 : ℝ)
  | ⟨35,_⟩ => (28946123 / 100000000 : ℝ)
  | ⟨36,_⟩ => (14491521 / 50000000 : ℝ)
  | ⟨37,_⟩ => (232159 / 800000 : ℝ)
  | ⟨38,_⟩ => (36320777 / 125000000 : ℝ)
  | ⟨39,_⟩ => (29093231 / 100000000 : ℝ)
  | ⟨40,_⟩ => (145648773 / 500000000 : ℝ)
  | ⟨41,_⟩ => (29166193 / 100000000 : ℝ)
  | ⟨42,_⟩ => (36503183 / 125000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12340Cell0 :
    0 ≤ cap12340 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12340 (parameters ⟨0,by decide⟩)
      (scalarRow12340.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12340 ⟨0,by decide⟩ ∧
    (scalarRow12340.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12340 ⟨0,by decide⟩ + (scalarRow12340.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12340.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12340.targetFrame := by
  norm_num [cap12340, scalarRow12340, sourceIndex, cell12340, BstLean.Part263.envelope, parameters]

theorem repair12340Cell1 :
    0 ≤ cap12340 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12340 (parameters ⟨1,by decide⟩)
      (scalarRow12340.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12340 ⟨1,by decide⟩ ∧
    (scalarRow12340.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12340 ⟨1,by decide⟩ + (scalarRow12340.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12340.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12340.targetFrame := by
  norm_num [cap12340, scalarRow12340, sourceIndex, cell12340, BstLean.Part263.envelope, parameters]

theorem repair12340Cell2 :
    0 ≤ cap12340 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12340 (parameters ⟨2,by decide⟩)
      (scalarRow12340.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12340 ⟨2,by decide⟩ ∧
    (scalarRow12340.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12340 ⟨2,by decide⟩ + (scalarRow12340.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12340.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12340.targetFrame := by
  norm_num [cap12340, scalarRow12340, sourceIndex, cell12340, BstLean.Part263.envelope, parameters]

theorem repair12340Cell3 :
    0 ≤ cap12340 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12340 (parameters ⟨3,by decide⟩)
      (scalarRow12340.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12340 ⟨3,by decide⟩ ∧
    (scalarRow12340.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12340 ⟨3,by decide⟩ + (scalarRow12340.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12340.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12340.targetFrame := by
  norm_num [cap12340, scalarRow12340, sourceIndex, cell12340, BstLean.Part263.envelope, parameters]

theorem repair12340Cell4 :
    0 ≤ cap12340 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12340 (parameters ⟨4,by decide⟩)
      (scalarRow12340.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12340 ⟨4,by decide⟩ ∧
    (scalarRow12340.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12340 ⟨4,by decide⟩ + (scalarRow12340.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12340.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12340.targetFrame := by
  norm_num [cap12340, scalarRow12340, sourceIndex, cell12340, BstLean.Part263.envelope, parameters]

theorem repair12340Cell5 :
    0 ≤ cap12340 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12340 (parameters ⟨5,by decide⟩)
      (scalarRow12340.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12340 ⟨5,by decide⟩ ∧
    (scalarRow12340.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12340 ⟨5,by decide⟩ + (scalarRow12340.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12340.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12340.targetFrame := by
  norm_num [cap12340, scalarRow12340, sourceIndex, cell12340, BstLean.Part263.envelope, parameters]

theorem repair12340Cell6 :
    0 ≤ cap12340 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12340 (parameters ⟨6,by decide⟩)
      (scalarRow12340.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12340 ⟨6,by decide⟩ ∧
    (scalarRow12340.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12340 ⟨6,by decide⟩ + (scalarRow12340.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12340.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12340.targetFrame := by
  norm_num [cap12340, scalarRow12340, sourceIndex, cell12340, BstLean.Part263.envelope, parameters]

theorem repair12340Cell7 :
    0 ≤ cap12340 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12340 (parameters ⟨7,by decide⟩)
      (scalarRow12340.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12340 ⟨7,by decide⟩ ∧
    (scalarRow12340.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12340 ⟨7,by decide⟩ + (scalarRow12340.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12340.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12340.targetFrame := by
  norm_num [cap12340, scalarRow12340, sourceIndex, cell12340, BstLean.Part263.envelope, parameters]

theorem repair12340Cell8 :
    0 ≤ cap12340 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12340 (parameters ⟨8,by decide⟩)
      (scalarRow12340.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12340 ⟨8,by decide⟩ ∧
    (scalarRow12340.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12340 ⟨8,by decide⟩ + (scalarRow12340.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12340.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12340.targetFrame := by
  norm_num [cap12340, scalarRow12340, sourceIndex, cell12340, BstLean.Part263.envelope, parameters]

theorem repair12340Cell9 :
    0 ≤ cap12340 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12340 (parameters ⟨9,by decide⟩)
      (scalarRow12340.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12340 ⟨9,by decide⟩ ∧
    (scalarRow12340.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12340 ⟨9,by decide⟩ + (scalarRow12340.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12340.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12340.targetFrame := by
  norm_num [cap12340, scalarRow12340, sourceIndex, cell12340, BstLean.Part263.envelope, parameters]

theorem repair12340Cell10 :
    0 ≤ cap12340 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12340 (parameters ⟨10,by decide⟩)
      (scalarRow12340.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12340 ⟨10,by decide⟩ ∧
    (scalarRow12340.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12340 ⟨10,by decide⟩ + (scalarRow12340.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12340.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12340.targetFrame := by
  norm_num [cap12340, scalarRow12340, sourceIndex, cell12340, BstLean.Part263.envelope, parameters]

theorem repair12340Cell11 :
    0 ≤ cap12340 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12340 (parameters ⟨11,by decide⟩)
      (scalarRow12340.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12340 ⟨11,by decide⟩ ∧
    (scalarRow12340.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12340 ⟨11,by decide⟩ + (scalarRow12340.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12340.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12340.targetFrame := by
  norm_num [cap12340, scalarRow12340, sourceIndex, cell12340, BstLean.Part263.envelope, parameters]

theorem repair12340Cell12 :
    0 ≤ cap12340 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12340 (parameters ⟨12,by decide⟩)
      (scalarRow12340.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12340 ⟨12,by decide⟩ ∧
    (scalarRow12340.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12340 ⟨12,by decide⟩ + (scalarRow12340.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12340.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12340.targetFrame := by
  norm_num [cap12340, scalarRow12340, sourceIndex, cell12340, BstLean.Part263.envelope, parameters]

theorem repair12340Cell13 :
    0 ≤ cap12340 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12340 (parameters ⟨13,by decide⟩)
      (scalarRow12340.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12340 ⟨13,by decide⟩ ∧
    (scalarRow12340.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12340 ⟨13,by decide⟩ + (scalarRow12340.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12340.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12340.targetFrame := by
  norm_num [cap12340, scalarRow12340, sourceIndex, cell12340, BstLean.Part263.envelope, parameters]

theorem repair12340Cell14 :
    0 ≤ cap12340 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12340 (parameters ⟨14,by decide⟩)
      (scalarRow12340.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12340 ⟨14,by decide⟩ ∧
    (scalarRow12340.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12340 ⟨14,by decide⟩ + (scalarRow12340.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12340.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12340.targetFrame := by
  norm_num [cap12340, scalarRow12340, sourceIndex, cell12340, BstLean.Part263.envelope, parameters]

theorem repair12340Cell15 :
    0 ≤ cap12340 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12340 (parameters ⟨15,by decide⟩)
      (scalarRow12340.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12340 ⟨15,by decide⟩ ∧
    (scalarRow12340.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12340 ⟨15,by decide⟩ + (scalarRow12340.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12340.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12340.targetFrame := by
  norm_num [cap12340, scalarRow12340, sourceIndex, cell12340, BstLean.Part263.envelope, parameters]

theorem repair12340Cell16 :
    0 ≤ cap12340 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12340 (parameters ⟨16,by decide⟩)
      (scalarRow12340.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12340 ⟨16,by decide⟩ ∧
    (scalarRow12340.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12340 ⟨16,by decide⟩ + (scalarRow12340.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12340.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12340.targetFrame := by
  norm_num [cap12340, scalarRow12340, sourceIndex, cell12340, BstLean.Part263.envelope, parameters]

theorem repair12340Cell17 :
    0 ≤ cap12340 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12340 (parameters ⟨17,by decide⟩)
      (scalarRow12340.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12340 ⟨17,by decide⟩ ∧
    (scalarRow12340.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12340 ⟨17,by decide⟩ + (scalarRow12340.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12340.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12340.targetFrame := by
  norm_num [cap12340, scalarRow12340, sourceIndex, cell12340, BstLean.Part263.envelope, parameters]

theorem repair12340Cell18 :
    0 ≤ cap12340 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12340 (parameters ⟨18,by decide⟩)
      (scalarRow12340.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12340 ⟨18,by decide⟩ ∧
    (scalarRow12340.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12340 ⟨18,by decide⟩ + (scalarRow12340.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12340.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12340.targetFrame := by
  norm_num [cap12340, scalarRow12340, sourceIndex, cell12340, BstLean.Part263.envelope, parameters]

theorem repair12340Cell19 :
    0 ≤ cap12340 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12340 (parameters ⟨19,by decide⟩)
      (scalarRow12340.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12340 ⟨19,by decide⟩ ∧
    (scalarRow12340.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12340 ⟨19,by decide⟩ + (scalarRow12340.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12340.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12340.targetFrame := by
  norm_num [cap12340, scalarRow12340, sourceIndex, cell12340, BstLean.Part263.envelope, parameters]

theorem repair12340Cell20 :
    0 ≤ cap12340 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12340 (parameters ⟨20,by decide⟩)
      (scalarRow12340.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12340 ⟨20,by decide⟩ ∧
    (scalarRow12340.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12340 ⟨20,by decide⟩ + (scalarRow12340.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12340.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12340.targetFrame := by
  norm_num [cap12340, scalarRow12340, sourceIndex, cell12340, BstLean.Part263.envelope, parameters]

theorem repair12340Cell21 :
    0 ≤ cap12340 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12340 (parameters ⟨21,by decide⟩)
      (scalarRow12340.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12340 ⟨21,by decide⟩ ∧
    (scalarRow12340.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12340 ⟨21,by decide⟩ + (scalarRow12340.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12340.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12340.targetFrame := by
  norm_num [cap12340, scalarRow12340, sourceIndex, cell12340, BstLean.Part263.envelope, parameters]

theorem repair12340Cell22 :
    0 ≤ cap12340 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12340 (parameters ⟨22,by decide⟩)
      (scalarRow12340.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12340 ⟨22,by decide⟩ ∧
    (scalarRow12340.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12340 ⟨22,by decide⟩ + (scalarRow12340.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12340.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12340.targetFrame := by
  norm_num [cap12340, scalarRow12340, sourceIndex, cell12340, BstLean.Part263.envelope, parameters]

theorem repair12340Cell23 :
    0 ≤ cap12340 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12340 (parameters ⟨23,by decide⟩)
      (scalarRow12340.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12340 ⟨23,by decide⟩ ∧
    (scalarRow12340.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12340 ⟨23,by decide⟩ + (scalarRow12340.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12340.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12340.targetFrame := by
  norm_num [cap12340, scalarRow12340, sourceIndex, cell12340, BstLean.Part263.envelope, parameters]

theorem repair12340Cell24 :
    0 ≤ cap12340 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12340 (parameters ⟨24,by decide⟩)
      (scalarRow12340.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12340 ⟨24,by decide⟩ ∧
    (scalarRow12340.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12340 ⟨24,by decide⟩ + (scalarRow12340.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12340.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12340.targetFrame := by
  norm_num [cap12340, scalarRow12340, sourceIndex, cell12340, BstLean.Part263.envelope, parameters]

theorem repair12340Cell25 :
    0 ≤ cap12340 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12340 (parameters ⟨25,by decide⟩)
      (scalarRow12340.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12340 ⟨25,by decide⟩ ∧
    (scalarRow12340.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12340 ⟨25,by decide⟩ + (scalarRow12340.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12340.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12340.targetFrame := by
  norm_num [cap12340, scalarRow12340, sourceIndex, cell12340, BstLean.Part263.envelope, parameters]

theorem repair12340Cell26 :
    0 ≤ cap12340 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12340 (parameters ⟨26,by decide⟩)
      (scalarRow12340.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12340 ⟨26,by decide⟩ ∧
    (scalarRow12340.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12340 ⟨26,by decide⟩ + (scalarRow12340.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12340.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12340.targetFrame := by
  norm_num [cap12340, scalarRow12340, sourceIndex, cell12340, BstLean.Part263.envelope, parameters]

theorem repair12340Cell27 :
    0 ≤ cap12340 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12340 (parameters ⟨27,by decide⟩)
      (scalarRow12340.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12340 ⟨27,by decide⟩ ∧
    (scalarRow12340.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12340 ⟨27,by decide⟩ + (scalarRow12340.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12340.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12340.targetFrame := by
  norm_num [cap12340, scalarRow12340, sourceIndex, cell12340, BstLean.Part263.envelope, parameters]

theorem repair12340Cell28 :
    0 ≤ cap12340 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12340 (parameters ⟨28,by decide⟩)
      (scalarRow12340.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12340 ⟨28,by decide⟩ ∧
    (scalarRow12340.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12340 ⟨28,by decide⟩ + (scalarRow12340.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12340.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12340.targetFrame := by
  norm_num [cap12340, scalarRow12340, sourceIndex, cell12340, BstLean.Part263.envelope, parameters]

theorem repair12340Cell29 :
    0 ≤ cap12340 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12340 (parameters ⟨29,by decide⟩)
      (scalarRow12340.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12340 ⟨29,by decide⟩ ∧
    (scalarRow12340.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12340 ⟨29,by decide⟩ + (scalarRow12340.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12340.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12340.targetFrame := by
  norm_num [cap12340, scalarRow12340, sourceIndex, cell12340, BstLean.Part263.envelope, parameters]

theorem repair12340Cell30 :
    0 ≤ cap12340 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12340 (parameters ⟨30,by decide⟩)
      (scalarRow12340.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12340 ⟨30,by decide⟩ ∧
    (scalarRow12340.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12340 ⟨30,by decide⟩ + (scalarRow12340.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12340.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12340.targetFrame := by
  norm_num [cap12340, scalarRow12340, sourceIndex, cell12340, BstLean.Part263.envelope, parameters]

theorem repair12340Cell31 :
    0 ≤ cap12340 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12340 (parameters ⟨31,by decide⟩)
      (scalarRow12340.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12340 ⟨31,by decide⟩ ∧
    (scalarRow12340.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12340 ⟨31,by decide⟩ + (scalarRow12340.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12340.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12340.targetFrame := by
  norm_num [cap12340, scalarRow12340, sourceIndex, cell12340, BstLean.Part263.envelope, parameters]

theorem repair12340Cell32 :
    0 ≤ cap12340 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12340 (parameters ⟨32,by decide⟩)
      (scalarRow12340.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12340 ⟨32,by decide⟩ ∧
    (scalarRow12340.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12340 ⟨32,by decide⟩ + (scalarRow12340.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12340.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12340.targetFrame := by
  norm_num [cap12340, scalarRow12340, sourceIndex, cell12340, BstLean.Part263.envelope, parameters]

theorem repair12340Cell33 :
    0 ≤ cap12340 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12340 (parameters ⟨33,by decide⟩)
      (scalarRow12340.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12340 ⟨33,by decide⟩ ∧
    (scalarRow12340.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12340 ⟨33,by decide⟩ + (scalarRow12340.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12340.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12340.targetFrame := by
  norm_num [cap12340, scalarRow12340, sourceIndex, cell12340, BstLean.Part263.envelope, parameters]

theorem repair12340Cell34 :
    0 ≤ cap12340 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12340 (parameters ⟨34,by decide⟩)
      (scalarRow12340.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12340 ⟨34,by decide⟩ ∧
    (scalarRow12340.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12340 ⟨34,by decide⟩ + (scalarRow12340.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12340.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12340.targetFrame := by
  norm_num [cap12340, scalarRow12340, sourceIndex, cell12340, BstLean.Part263.envelope, parameters]

theorem repair12340Cell35 :
    0 ≤ cap12340 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12340 (parameters ⟨35,by decide⟩)
      (scalarRow12340.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12340 ⟨35,by decide⟩ ∧
    (scalarRow12340.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12340 ⟨35,by decide⟩ + (scalarRow12340.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12340.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12340.targetFrame := by
  norm_num [cap12340, scalarRow12340, sourceIndex, cell12340, BstLean.Part263.envelope, parameters]

theorem repair12340Cell36 :
    0 ≤ cap12340 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12340 (parameters ⟨36,by decide⟩)
      (scalarRow12340.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12340 ⟨36,by decide⟩ ∧
    (scalarRow12340.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12340 ⟨36,by decide⟩ + (scalarRow12340.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12340.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12340.targetFrame := by
  norm_num [cap12340, scalarRow12340, sourceIndex, cell12340, BstLean.Part263.envelope, parameters]

theorem repair12340Cell37 :
    0 ≤ cap12340 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12340 (parameters ⟨37,by decide⟩)
      (scalarRow12340.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12340 ⟨37,by decide⟩ ∧
    (scalarRow12340.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12340 ⟨37,by decide⟩ + (scalarRow12340.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12340.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12340.targetFrame := by
  norm_num [cap12340, scalarRow12340, sourceIndex, cell12340, BstLean.Part263.envelope, parameters]

theorem repair12340Cell38 :
    0 ≤ cap12340 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12340 (parameters ⟨38,by decide⟩)
      (scalarRow12340.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12340 ⟨38,by decide⟩ ∧
    (scalarRow12340.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12340 ⟨38,by decide⟩ + (scalarRow12340.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12340.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12340.targetFrame := by
  norm_num [cap12340, scalarRow12340, sourceIndex, cell12340, BstLean.Part263.envelope, parameters]

theorem repair12340Cell39 :
    0 ≤ cap12340 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12340 (parameters ⟨39,by decide⟩)
      (scalarRow12340.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12340 ⟨39,by decide⟩ ∧
    (scalarRow12340.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12340 ⟨39,by decide⟩ + (scalarRow12340.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12340.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12340.targetFrame := by
  norm_num [cap12340, scalarRow12340, sourceIndex, cell12340, BstLean.Part263.envelope, parameters]

theorem repair12340Cell40 :
    0 ≤ cap12340 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12340 (parameters ⟨40,by decide⟩)
      (scalarRow12340.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12340 ⟨40,by decide⟩ ∧
    (scalarRow12340.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12340 ⟨40,by decide⟩ + (scalarRow12340.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12340.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12340.targetFrame := by
  norm_num [cap12340, scalarRow12340, sourceIndex, cell12340, BstLean.Part263.envelope, parameters]

theorem repair12340Cell41 :
    0 ≤ cap12340 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12340 (parameters ⟨41,by decide⟩)
      (scalarRow12340.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12340 ⟨41,by decide⟩ ∧
    (scalarRow12340.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12340 ⟨41,by decide⟩ + (scalarRow12340.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12340.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12340.targetFrame := by
  norm_num [cap12340, scalarRow12340, sourceIndex, cell12340, BstLean.Part263.envelope, parameters]

theorem repair12340Cell42 :
    0 ≤ cap12340 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12340 (parameters ⟨42,by decide⟩)
      (scalarRow12340.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12340 ⟨42,by decide⟩ ∧
    (scalarRow12340.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12340 ⟨42,by decide⟩ + (scalarRow12340.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12340.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12340.targetFrame := by
  norm_num [cap12340, scalarRow12340, sourceIndex, cell12340, BstLean.Part263.envelope, parameters]

theorem repair12340Cells (j : Fin 43) :
    0 ≤ cap12340 j ∧
    BstLean.Part263.envelope 12340 (parameters j) (scalarRow12340.table (sourceIndex j)).upper ≤ cap12340 j ∧
    (scalarRow12340.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12340 j + (scalarRow12340.table (sourceIndex j)).centre) /
      (scalarRow12340.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12340.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12340Cell0
  | ⟨1,_⟩ => exact repair12340Cell1
  | ⟨2,_⟩ => exact repair12340Cell2
  | ⟨3,_⟩ => exact repair12340Cell3
  | ⟨4,_⟩ => exact repair12340Cell4
  | ⟨5,_⟩ => exact repair12340Cell5
  | ⟨6,_⟩ => exact repair12340Cell6
  | ⟨7,_⟩ => exact repair12340Cell7
  | ⟨8,_⟩ => exact repair12340Cell8
  | ⟨9,_⟩ => exact repair12340Cell9
  | ⟨10,_⟩ => exact repair12340Cell10
  | ⟨11,_⟩ => exact repair12340Cell11
  | ⟨12,_⟩ => exact repair12340Cell12
  | ⟨13,_⟩ => exact repair12340Cell13
  | ⟨14,_⟩ => exact repair12340Cell14
  | ⟨15,_⟩ => exact repair12340Cell15
  | ⟨16,_⟩ => exact repair12340Cell16
  | ⟨17,_⟩ => exact repair12340Cell17
  | ⟨18,_⟩ => exact repair12340Cell18
  | ⟨19,_⟩ => exact repair12340Cell19
  | ⟨20,_⟩ => exact repair12340Cell20
  | ⟨21,_⟩ => exact repair12340Cell21
  | ⟨22,_⟩ => exact repair12340Cell22
  | ⟨23,_⟩ => exact repair12340Cell23
  | ⟨24,_⟩ => exact repair12340Cell24
  | ⟨25,_⟩ => exact repair12340Cell25
  | ⟨26,_⟩ => exact repair12340Cell26
  | ⟨27,_⟩ => exact repair12340Cell27
  | ⟨28,_⟩ => exact repair12340Cell28
  | ⟨29,_⟩ => exact repair12340Cell29
  | ⟨30,_⟩ => exact repair12340Cell30
  | ⟨31,_⟩ => exact repair12340Cell31
  | ⟨32,_⟩ => exact repair12340Cell32
  | ⟨33,_⟩ => exact repair12340Cell33
  | ⟨34,_⟩ => exact repair12340Cell34
  | ⟨35,_⟩ => exact repair12340Cell35
  | ⟨36,_⟩ => exact repair12340Cell36
  | ⟨37,_⟩ => exact repair12340Cell37
  | ⟨38,_⟩ => exact repair12340Cell38
  | ⟨39,_⟩ => exact repair12340Cell39
  | ⟨40,_⟩ => exact repair12340Cell40
  | ⟨41,_⟩ => exact repair12340Cell41
  | ⟨42,_⟩ => exact repair12340Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12340 : FrameRepair 12340 scalarRow12340 where
  cap := cap12340
  cap_nonneg := fun j => (repair12340Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12340])
  endpoint := fun j => (repair12340Cells j).2.1
  endpoint_upper := fun j => (repair12340Cells j).2.2.1
  frame := fun j => (repair12340Cells j).2.2.2

noncomputable def cap12341 : Fin 43 → ℝ
  | ⟨0,_⟩ => (275943977 / 1000000000 : ℝ)
  | ⟨1,_⟩ => (276346497 / 1000000000 : ℝ)
  | ⟨2,_⟩ => (34593503 / 125000000 : ℝ)
  | ⟨3,_⟩ => (138574277 / 500000000 : ℝ)
  | ⟨4,_⟩ => (138774047 / 500000000 : ℝ)
  | ⟨5,_⟩ => (55589329 / 200000000 : ℝ)
  | ⟨6,_⟩ => (34792967 / 125000000 : ℝ)
  | ⟨7,_⟩ => (278740321 / 1000000000 : ℝ)
  | ⟨8,_⟩ => (279135931 / 1000000000 : ℝ)
  | ⟨9,_⟩ => (27953057 / 100000000 : ℝ)
  | ⟨10,_⟩ => (279924239 / 1000000000 : ℝ)
  | ⟨11,_⟩ => (280316459 / 1000000000 : ℝ)
  | ⟨12,_⟩ => (280708203 / 1000000000 : ℝ)
  | ⟨13,_⟩ => (281098501 / 1000000000 : ℝ)
  | ⟨14,_⟩ => (70372183 / 250000000 : ℝ)
  | ⟨15,_⟩ => (35234733 / 125000000 : ℝ)
  | ⟨16,_⟩ => (282266053 / 1000000000 : ℝ)
  | ⟨17,_⟩ => (282653313 / 1000000000 : ℝ)
  | ⟨18,_⟩ => (283039633 / 1000000000 : ℝ)
  | ⟨19,_⟩ => (141712513 / 500000000 : ℝ)
  | ⟨20,_⟩ => (70952373 / 250000000 : ℝ)
  | ⟨21,_⟩ => (284193043 / 1000000000 : ℝ)
  | ⟨22,_⟩ => (28457567 / 100000000 : ℝ)
  | ⟨23,_⟩ => (284956887 / 1000000000 : ℝ)
  | ⟨24,_⟩ => (71334423 / 250000000 : ℝ)
  | ⟨25,_⟩ => (285717137 / 1000000000 : ℝ)
  | ⟨26,_⟩ => (143048089 / 500000000 : ℝ)
  | ⟨27,_⟩ => (14323691 / 50000000 : ℝ)
  | ⟨28,_⟩ => (143425283 / 500000000 : ℝ)
  | ⟨29,_⟩ => (287226417 / 1000000000 : ℝ)
  | ⟨30,_⟩ => (2300807 / 8000000 : ℝ)
  | ⟨31,_⟩ => (5759499 / 20000000 : ℝ)
  | ⟨32,_⟩ => (18021759 / 62500000 : ℝ)
  | ⟨33,_⟩ => (288719949 / 1000000000 : ℝ)
  | ⟨34,_⟩ => (289090879 / 1000000000 : ℝ)
  | ⟨35,_⟩ => (144730469 / 500000000 : ℝ)
  | ⟨36,_⟩ => (289830121 / 1000000000 : ℝ)
  | ⟨37,_⟩ => (145099223 / 500000000 : ℝ)
  | ⟨38,_⟩ => (145282953 / 500000000 : ℝ)
  | ⟨39,_⟩ => (145465997 / 500000000 : ℝ)
  | ⟨40,_⟩ => (36412153 / 125000000 : ℝ)
  | ⟨41,_⟩ => (145830801 / 500000000 : ℝ)
  | ⟨42,_⟩ => (29202513 / 100000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12341Cell0 :
    0 ≤ cap12341 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12341 (parameters ⟨0,by decide⟩)
      (scalarRow12341.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12341 ⟨0,by decide⟩ ∧
    (scalarRow12341.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12341 ⟨0,by decide⟩ + (scalarRow12341.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12341.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12341.targetFrame := by
  norm_num [cap12341, scalarRow12341, sourceIndex, cell12341, BstLean.Part263.envelope, parameters]

theorem repair12341Cell1 :
    0 ≤ cap12341 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12341 (parameters ⟨1,by decide⟩)
      (scalarRow12341.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12341 ⟨1,by decide⟩ ∧
    (scalarRow12341.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12341 ⟨1,by decide⟩ + (scalarRow12341.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12341.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12341.targetFrame := by
  norm_num [cap12341, scalarRow12341, sourceIndex, cell12341, BstLean.Part263.envelope, parameters]

theorem repair12341Cell2 :
    0 ≤ cap12341 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12341 (parameters ⟨2,by decide⟩)
      (scalarRow12341.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12341 ⟨2,by decide⟩ ∧
    (scalarRow12341.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12341 ⟨2,by decide⟩ + (scalarRow12341.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12341.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12341.targetFrame := by
  norm_num [cap12341, scalarRow12341, sourceIndex, cell12341, BstLean.Part263.envelope, parameters]

theorem repair12341Cell3 :
    0 ≤ cap12341 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12341 (parameters ⟨3,by decide⟩)
      (scalarRow12341.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12341 ⟨3,by decide⟩ ∧
    (scalarRow12341.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12341 ⟨3,by decide⟩ + (scalarRow12341.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12341.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12341.targetFrame := by
  norm_num [cap12341, scalarRow12341, sourceIndex, cell12341, BstLean.Part263.envelope, parameters]

theorem repair12341Cell4 :
    0 ≤ cap12341 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12341 (parameters ⟨4,by decide⟩)
      (scalarRow12341.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12341 ⟨4,by decide⟩ ∧
    (scalarRow12341.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12341 ⟨4,by decide⟩ + (scalarRow12341.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12341.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12341.targetFrame := by
  norm_num [cap12341, scalarRow12341, sourceIndex, cell12341, BstLean.Part263.envelope, parameters]

theorem repair12341Cell5 :
    0 ≤ cap12341 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12341 (parameters ⟨5,by decide⟩)
      (scalarRow12341.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12341 ⟨5,by decide⟩ ∧
    (scalarRow12341.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12341 ⟨5,by decide⟩ + (scalarRow12341.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12341.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12341.targetFrame := by
  norm_num [cap12341, scalarRow12341, sourceIndex, cell12341, BstLean.Part263.envelope, parameters]

theorem repair12341Cell6 :
    0 ≤ cap12341 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12341 (parameters ⟨6,by decide⟩)
      (scalarRow12341.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12341 ⟨6,by decide⟩ ∧
    (scalarRow12341.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12341 ⟨6,by decide⟩ + (scalarRow12341.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12341.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12341.targetFrame := by
  norm_num [cap12341, scalarRow12341, sourceIndex, cell12341, BstLean.Part263.envelope, parameters]

theorem repair12341Cell7 :
    0 ≤ cap12341 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12341 (parameters ⟨7,by decide⟩)
      (scalarRow12341.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12341 ⟨7,by decide⟩ ∧
    (scalarRow12341.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12341 ⟨7,by decide⟩ + (scalarRow12341.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12341.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12341.targetFrame := by
  norm_num [cap12341, scalarRow12341, sourceIndex, cell12341, BstLean.Part263.envelope, parameters]

theorem repair12341Cell8 :
    0 ≤ cap12341 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12341 (parameters ⟨8,by decide⟩)
      (scalarRow12341.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12341 ⟨8,by decide⟩ ∧
    (scalarRow12341.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12341 ⟨8,by decide⟩ + (scalarRow12341.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12341.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12341.targetFrame := by
  norm_num [cap12341, scalarRow12341, sourceIndex, cell12341, BstLean.Part263.envelope, parameters]

theorem repair12341Cell9 :
    0 ≤ cap12341 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12341 (parameters ⟨9,by decide⟩)
      (scalarRow12341.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12341 ⟨9,by decide⟩ ∧
    (scalarRow12341.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12341 ⟨9,by decide⟩ + (scalarRow12341.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12341.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12341.targetFrame := by
  norm_num [cap12341, scalarRow12341, sourceIndex, cell12341, BstLean.Part263.envelope, parameters]

theorem repair12341Cell10 :
    0 ≤ cap12341 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12341 (parameters ⟨10,by decide⟩)
      (scalarRow12341.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12341 ⟨10,by decide⟩ ∧
    (scalarRow12341.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12341 ⟨10,by decide⟩ + (scalarRow12341.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12341.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12341.targetFrame := by
  norm_num [cap12341, scalarRow12341, sourceIndex, cell12341, BstLean.Part263.envelope, parameters]

theorem repair12341Cell11 :
    0 ≤ cap12341 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12341 (parameters ⟨11,by decide⟩)
      (scalarRow12341.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12341 ⟨11,by decide⟩ ∧
    (scalarRow12341.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12341 ⟨11,by decide⟩ + (scalarRow12341.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12341.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12341.targetFrame := by
  norm_num [cap12341, scalarRow12341, sourceIndex, cell12341, BstLean.Part263.envelope, parameters]

theorem repair12341Cell12 :
    0 ≤ cap12341 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12341 (parameters ⟨12,by decide⟩)
      (scalarRow12341.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12341 ⟨12,by decide⟩ ∧
    (scalarRow12341.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12341 ⟨12,by decide⟩ + (scalarRow12341.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12341.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12341.targetFrame := by
  norm_num [cap12341, scalarRow12341, sourceIndex, cell12341, BstLean.Part263.envelope, parameters]

theorem repair12341Cell13 :
    0 ≤ cap12341 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12341 (parameters ⟨13,by decide⟩)
      (scalarRow12341.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12341 ⟨13,by decide⟩ ∧
    (scalarRow12341.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12341 ⟨13,by decide⟩ + (scalarRow12341.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12341.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12341.targetFrame := by
  norm_num [cap12341, scalarRow12341, sourceIndex, cell12341, BstLean.Part263.envelope, parameters]

theorem repair12341Cell14 :
    0 ≤ cap12341 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12341 (parameters ⟨14,by decide⟩)
      (scalarRow12341.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12341 ⟨14,by decide⟩ ∧
    (scalarRow12341.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12341 ⟨14,by decide⟩ + (scalarRow12341.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12341.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12341.targetFrame := by
  norm_num [cap12341, scalarRow12341, sourceIndex, cell12341, BstLean.Part263.envelope, parameters]

theorem repair12341Cell15 :
    0 ≤ cap12341 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12341 (parameters ⟨15,by decide⟩)
      (scalarRow12341.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12341 ⟨15,by decide⟩ ∧
    (scalarRow12341.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12341 ⟨15,by decide⟩ + (scalarRow12341.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12341.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12341.targetFrame := by
  norm_num [cap12341, scalarRow12341, sourceIndex, cell12341, BstLean.Part263.envelope, parameters]

theorem repair12341Cell16 :
    0 ≤ cap12341 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12341 (parameters ⟨16,by decide⟩)
      (scalarRow12341.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12341 ⟨16,by decide⟩ ∧
    (scalarRow12341.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12341 ⟨16,by decide⟩ + (scalarRow12341.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12341.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12341.targetFrame := by
  norm_num [cap12341, scalarRow12341, sourceIndex, cell12341, BstLean.Part263.envelope, parameters]

theorem repair12341Cell17 :
    0 ≤ cap12341 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12341 (parameters ⟨17,by decide⟩)
      (scalarRow12341.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12341 ⟨17,by decide⟩ ∧
    (scalarRow12341.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12341 ⟨17,by decide⟩ + (scalarRow12341.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12341.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12341.targetFrame := by
  norm_num [cap12341, scalarRow12341, sourceIndex, cell12341, BstLean.Part263.envelope, parameters]

theorem repair12341Cell18 :
    0 ≤ cap12341 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12341 (parameters ⟨18,by decide⟩)
      (scalarRow12341.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12341 ⟨18,by decide⟩ ∧
    (scalarRow12341.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12341 ⟨18,by decide⟩ + (scalarRow12341.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12341.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12341.targetFrame := by
  norm_num [cap12341, scalarRow12341, sourceIndex, cell12341, BstLean.Part263.envelope, parameters]

theorem repair12341Cell19 :
    0 ≤ cap12341 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12341 (parameters ⟨19,by decide⟩)
      (scalarRow12341.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12341 ⟨19,by decide⟩ ∧
    (scalarRow12341.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12341 ⟨19,by decide⟩ + (scalarRow12341.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12341.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12341.targetFrame := by
  norm_num [cap12341, scalarRow12341, sourceIndex, cell12341, BstLean.Part263.envelope, parameters]

theorem repair12341Cell20 :
    0 ≤ cap12341 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12341 (parameters ⟨20,by decide⟩)
      (scalarRow12341.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12341 ⟨20,by decide⟩ ∧
    (scalarRow12341.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12341 ⟨20,by decide⟩ + (scalarRow12341.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12341.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12341.targetFrame := by
  norm_num [cap12341, scalarRow12341, sourceIndex, cell12341, BstLean.Part263.envelope, parameters]

theorem repair12341Cell21 :
    0 ≤ cap12341 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12341 (parameters ⟨21,by decide⟩)
      (scalarRow12341.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12341 ⟨21,by decide⟩ ∧
    (scalarRow12341.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12341 ⟨21,by decide⟩ + (scalarRow12341.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12341.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12341.targetFrame := by
  norm_num [cap12341, scalarRow12341, sourceIndex, cell12341, BstLean.Part263.envelope, parameters]

theorem repair12341Cell22 :
    0 ≤ cap12341 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12341 (parameters ⟨22,by decide⟩)
      (scalarRow12341.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12341 ⟨22,by decide⟩ ∧
    (scalarRow12341.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12341 ⟨22,by decide⟩ + (scalarRow12341.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12341.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12341.targetFrame := by
  norm_num [cap12341, scalarRow12341, sourceIndex, cell12341, BstLean.Part263.envelope, parameters]

theorem repair12341Cell23 :
    0 ≤ cap12341 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12341 (parameters ⟨23,by decide⟩)
      (scalarRow12341.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12341 ⟨23,by decide⟩ ∧
    (scalarRow12341.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12341 ⟨23,by decide⟩ + (scalarRow12341.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12341.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12341.targetFrame := by
  norm_num [cap12341, scalarRow12341, sourceIndex, cell12341, BstLean.Part263.envelope, parameters]

theorem repair12341Cell24 :
    0 ≤ cap12341 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12341 (parameters ⟨24,by decide⟩)
      (scalarRow12341.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12341 ⟨24,by decide⟩ ∧
    (scalarRow12341.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12341 ⟨24,by decide⟩ + (scalarRow12341.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12341.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12341.targetFrame := by
  norm_num [cap12341, scalarRow12341, sourceIndex, cell12341, BstLean.Part263.envelope, parameters]

theorem repair12341Cell25 :
    0 ≤ cap12341 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12341 (parameters ⟨25,by decide⟩)
      (scalarRow12341.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12341 ⟨25,by decide⟩ ∧
    (scalarRow12341.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12341 ⟨25,by decide⟩ + (scalarRow12341.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12341.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12341.targetFrame := by
  norm_num [cap12341, scalarRow12341, sourceIndex, cell12341, BstLean.Part263.envelope, parameters]

theorem repair12341Cell26 :
    0 ≤ cap12341 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12341 (parameters ⟨26,by decide⟩)
      (scalarRow12341.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12341 ⟨26,by decide⟩ ∧
    (scalarRow12341.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12341 ⟨26,by decide⟩ + (scalarRow12341.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12341.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12341.targetFrame := by
  norm_num [cap12341, scalarRow12341, sourceIndex, cell12341, BstLean.Part263.envelope, parameters]

theorem repair12341Cell27 :
    0 ≤ cap12341 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12341 (parameters ⟨27,by decide⟩)
      (scalarRow12341.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12341 ⟨27,by decide⟩ ∧
    (scalarRow12341.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12341 ⟨27,by decide⟩ + (scalarRow12341.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12341.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12341.targetFrame := by
  norm_num [cap12341, scalarRow12341, sourceIndex, cell12341, BstLean.Part263.envelope, parameters]

theorem repair12341Cell28 :
    0 ≤ cap12341 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12341 (parameters ⟨28,by decide⟩)
      (scalarRow12341.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12341 ⟨28,by decide⟩ ∧
    (scalarRow12341.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12341 ⟨28,by decide⟩ + (scalarRow12341.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12341.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12341.targetFrame := by
  norm_num [cap12341, scalarRow12341, sourceIndex, cell12341, BstLean.Part263.envelope, parameters]

theorem repair12341Cell29 :
    0 ≤ cap12341 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12341 (parameters ⟨29,by decide⟩)
      (scalarRow12341.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12341 ⟨29,by decide⟩ ∧
    (scalarRow12341.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12341 ⟨29,by decide⟩ + (scalarRow12341.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12341.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12341.targetFrame := by
  norm_num [cap12341, scalarRow12341, sourceIndex, cell12341, BstLean.Part263.envelope, parameters]

theorem repair12341Cell30 :
    0 ≤ cap12341 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12341 (parameters ⟨30,by decide⟩)
      (scalarRow12341.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12341 ⟨30,by decide⟩ ∧
    (scalarRow12341.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12341 ⟨30,by decide⟩ + (scalarRow12341.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12341.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12341.targetFrame := by
  norm_num [cap12341, scalarRow12341, sourceIndex, cell12341, BstLean.Part263.envelope, parameters]

theorem repair12341Cell31 :
    0 ≤ cap12341 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12341 (parameters ⟨31,by decide⟩)
      (scalarRow12341.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12341 ⟨31,by decide⟩ ∧
    (scalarRow12341.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12341 ⟨31,by decide⟩ + (scalarRow12341.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12341.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12341.targetFrame := by
  norm_num [cap12341, scalarRow12341, sourceIndex, cell12341, BstLean.Part263.envelope, parameters]

theorem repair12341Cell32 :
    0 ≤ cap12341 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12341 (parameters ⟨32,by decide⟩)
      (scalarRow12341.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12341 ⟨32,by decide⟩ ∧
    (scalarRow12341.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12341 ⟨32,by decide⟩ + (scalarRow12341.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12341.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12341.targetFrame := by
  norm_num [cap12341, scalarRow12341, sourceIndex, cell12341, BstLean.Part263.envelope, parameters]

theorem repair12341Cell33 :
    0 ≤ cap12341 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12341 (parameters ⟨33,by decide⟩)
      (scalarRow12341.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12341 ⟨33,by decide⟩ ∧
    (scalarRow12341.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12341 ⟨33,by decide⟩ + (scalarRow12341.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12341.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12341.targetFrame := by
  norm_num [cap12341, scalarRow12341, sourceIndex, cell12341, BstLean.Part263.envelope, parameters]

theorem repair12341Cell34 :
    0 ≤ cap12341 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12341 (parameters ⟨34,by decide⟩)
      (scalarRow12341.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12341 ⟨34,by decide⟩ ∧
    (scalarRow12341.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12341 ⟨34,by decide⟩ + (scalarRow12341.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12341.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12341.targetFrame := by
  norm_num [cap12341, scalarRow12341, sourceIndex, cell12341, BstLean.Part263.envelope, parameters]

theorem repair12341Cell35 :
    0 ≤ cap12341 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12341 (parameters ⟨35,by decide⟩)
      (scalarRow12341.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12341 ⟨35,by decide⟩ ∧
    (scalarRow12341.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12341 ⟨35,by decide⟩ + (scalarRow12341.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12341.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12341.targetFrame := by
  norm_num [cap12341, scalarRow12341, sourceIndex, cell12341, BstLean.Part263.envelope, parameters]

theorem repair12341Cell36 :
    0 ≤ cap12341 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12341 (parameters ⟨36,by decide⟩)
      (scalarRow12341.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12341 ⟨36,by decide⟩ ∧
    (scalarRow12341.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12341 ⟨36,by decide⟩ + (scalarRow12341.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12341.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12341.targetFrame := by
  norm_num [cap12341, scalarRow12341, sourceIndex, cell12341, BstLean.Part263.envelope, parameters]

theorem repair12341Cell37 :
    0 ≤ cap12341 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12341 (parameters ⟨37,by decide⟩)
      (scalarRow12341.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12341 ⟨37,by decide⟩ ∧
    (scalarRow12341.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12341 ⟨37,by decide⟩ + (scalarRow12341.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12341.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12341.targetFrame := by
  norm_num [cap12341, scalarRow12341, sourceIndex, cell12341, BstLean.Part263.envelope, parameters]

theorem repair12341Cell38 :
    0 ≤ cap12341 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12341 (parameters ⟨38,by decide⟩)
      (scalarRow12341.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12341 ⟨38,by decide⟩ ∧
    (scalarRow12341.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12341 ⟨38,by decide⟩ + (scalarRow12341.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12341.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12341.targetFrame := by
  norm_num [cap12341, scalarRow12341, sourceIndex, cell12341, BstLean.Part263.envelope, parameters]

theorem repair12341Cell39 :
    0 ≤ cap12341 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12341 (parameters ⟨39,by decide⟩)
      (scalarRow12341.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12341 ⟨39,by decide⟩ ∧
    (scalarRow12341.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12341 ⟨39,by decide⟩ + (scalarRow12341.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12341.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12341.targetFrame := by
  norm_num [cap12341, scalarRow12341, sourceIndex, cell12341, BstLean.Part263.envelope, parameters]

theorem repair12341Cell40 :
    0 ≤ cap12341 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12341 (parameters ⟨40,by decide⟩)
      (scalarRow12341.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12341 ⟨40,by decide⟩ ∧
    (scalarRow12341.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12341 ⟨40,by decide⟩ + (scalarRow12341.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12341.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12341.targetFrame := by
  norm_num [cap12341, scalarRow12341, sourceIndex, cell12341, BstLean.Part263.envelope, parameters]

theorem repair12341Cell41 :
    0 ≤ cap12341 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12341 (parameters ⟨41,by decide⟩)
      (scalarRow12341.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12341 ⟨41,by decide⟩ ∧
    (scalarRow12341.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12341 ⟨41,by decide⟩ + (scalarRow12341.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12341.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12341.targetFrame := by
  norm_num [cap12341, scalarRow12341, sourceIndex, cell12341, BstLean.Part263.envelope, parameters]

theorem repair12341Cell42 :
    0 ≤ cap12341 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12341 (parameters ⟨42,by decide⟩)
      (scalarRow12341.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12341 ⟨42,by decide⟩ ∧
    (scalarRow12341.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12341 ⟨42,by decide⟩ + (scalarRow12341.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12341.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12341.targetFrame := by
  norm_num [cap12341, scalarRow12341, sourceIndex, cell12341, BstLean.Part263.envelope, parameters]

theorem repair12341Cells (j : Fin 43) :
    0 ≤ cap12341 j ∧
    BstLean.Part263.envelope 12341 (parameters j) (scalarRow12341.table (sourceIndex j)).upper ≤ cap12341 j ∧
    (scalarRow12341.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12341 j + (scalarRow12341.table (sourceIndex j)).centre) /
      (scalarRow12341.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12341.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12341Cell0
  | ⟨1,_⟩ => exact repair12341Cell1
  | ⟨2,_⟩ => exact repair12341Cell2
  | ⟨3,_⟩ => exact repair12341Cell3
  | ⟨4,_⟩ => exact repair12341Cell4
  | ⟨5,_⟩ => exact repair12341Cell5
  | ⟨6,_⟩ => exact repair12341Cell6
  | ⟨7,_⟩ => exact repair12341Cell7
  | ⟨8,_⟩ => exact repair12341Cell8
  | ⟨9,_⟩ => exact repair12341Cell9
  | ⟨10,_⟩ => exact repair12341Cell10
  | ⟨11,_⟩ => exact repair12341Cell11
  | ⟨12,_⟩ => exact repair12341Cell12
  | ⟨13,_⟩ => exact repair12341Cell13
  | ⟨14,_⟩ => exact repair12341Cell14
  | ⟨15,_⟩ => exact repair12341Cell15
  | ⟨16,_⟩ => exact repair12341Cell16
  | ⟨17,_⟩ => exact repair12341Cell17
  | ⟨18,_⟩ => exact repair12341Cell18
  | ⟨19,_⟩ => exact repair12341Cell19
  | ⟨20,_⟩ => exact repair12341Cell20
  | ⟨21,_⟩ => exact repair12341Cell21
  | ⟨22,_⟩ => exact repair12341Cell22
  | ⟨23,_⟩ => exact repair12341Cell23
  | ⟨24,_⟩ => exact repair12341Cell24
  | ⟨25,_⟩ => exact repair12341Cell25
  | ⟨26,_⟩ => exact repair12341Cell26
  | ⟨27,_⟩ => exact repair12341Cell27
  | ⟨28,_⟩ => exact repair12341Cell28
  | ⟨29,_⟩ => exact repair12341Cell29
  | ⟨30,_⟩ => exact repair12341Cell30
  | ⟨31,_⟩ => exact repair12341Cell31
  | ⟨32,_⟩ => exact repair12341Cell32
  | ⟨33,_⟩ => exact repair12341Cell33
  | ⟨34,_⟩ => exact repair12341Cell34
  | ⟨35,_⟩ => exact repair12341Cell35
  | ⟨36,_⟩ => exact repair12341Cell36
  | ⟨37,_⟩ => exact repair12341Cell37
  | ⟨38,_⟩ => exact repair12341Cell38
  | ⟨39,_⟩ => exact repair12341Cell39
  | ⟨40,_⟩ => exact repair12341Cell40
  | ⟨41,_⟩ => exact repair12341Cell41
  | ⟨42,_⟩ => exact repair12341Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12341 : FrameRepair 12341 scalarRow12341 where
  cap := cap12341
  cap_nonneg := fun j => (repair12341Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12341])
  endpoint := fun j => (repair12341Cells j).2.1
  endpoint_upper := fun j => (repair12341Cells j).2.2.1
  frame := fun j => (repair12341Cells j).2.2.2

noncomputable def cap12342 : Fin 43 → ℝ
  | ⟨0,_⟩ => (137971951 / 500000000 : ℝ)
  | ⟨1,_⟩ => (17271651 / 62500000 : ℝ)
  | ⟨2,_⟩ => (8648373 / 31250000 : ℝ)
  | ⟨3,_⟩ => (277148459 / 1000000000 : ℝ)
  | ⟨4,_⟩ => (277547993 / 1000000000 : ℝ)
  | ⟨5,_⟩ => (138973269 / 500000000 : ℝ)
  | ⟨6,_⟩ => (139171811 / 500000000 : ℝ)
  | ⟨7,_⟩ => (278740201 / 1000000000 : ℝ)
  | ⟨8,_⟩ => (55827161 / 200000000 : ℝ)
  | ⟨9,_⟩ => (139765219 / 500000000 : ℝ)
  | ⟨10,_⟩ => (2799241 / 10000000 : ℝ)
  | ⟨11,_⟩ => (140158157 / 500000000 : ℝ)
  | ⟨12,_⟩ => (70177013 / 250000000 : ℝ)
  | ⟨13,_⟩ => (281098343 / 1000000000 : ℝ)
  | ⟨14,_⟩ => (35186071 / 125000000 : ℝ)
  | ⟨15,_⟩ => (281877693 / 1000000000 : ℝ)
  | ⟨16,_⟩ => (282265877 / 1000000000 : ℝ)
  | ⟨17,_⟩ => (28265313 / 100000000 : ℝ)
  | ⟨18,_⟩ => (56607889 / 200000000 : ℝ)
  | ⟨19,_⟩ => (283424831 / 1000000000 : ℝ)
  | ⟨20,_⟩ => (283809291 / 1000000000 : ℝ)
  | ⟨21,_⟩ => (56838567 / 200000000 : ℝ)
  | ⟨22,_⟩ => (284575457 / 1000000000 : ℝ)
  | ⟨23,_⟩ => (71239167 / 250000000 : ℝ)
  | ⟨24,_⟩ => (142668733 / 500000000 : ℝ)
  | ⟨25,_⟩ => (57143381 / 200000000 : ℝ)
  | ⟨26,_⟩ => (14304797 / 50000000 : ℝ)
  | ⟨27,_⟩ => (35809197 / 125000000 : ℝ)
  | ⟨28,_⟩ => (71712579 / 250000000 : ℝ)
  | ⟨29,_⟩ => (287226161 / 1000000000 : ℝ)
  | ⟨30,_⟩ => (287600613 / 1000000000 : ℝ)
  | ⟨31,_⟩ => (143987341 / 500000000 : ℝ)
  | ⟨32,_⟩ => (28834787 / 100000000 : ℝ)
  | ⟨33,_⟩ => (288719669 / 1000000000 : ℝ)
  | ⟨34,_⟩ => (289090593 / 1000000000 : ℝ)
  | ⟨35,_⟩ => (144730323 / 500000000 : ℝ)
  | ⟨36,_⟩ => (289829823 / 1000000000 : ℝ)
  | ⟨37,_⟩ => (145099071 / 500000000 : ℝ)
  | ⟨38,_⟩ => (72641399 / 250000000 : ℝ)
  | ⟨39,_⟩ => (145465839 / 500000000 : ℝ)
  | ⟨40,_⟩ => (145648451 / 500000000 : ℝ)
  | ⟨41,_⟩ => (11666451 / 40000000 : ℝ)
  | ⟨42,_⟩ => (73006199 / 250000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12342Cell0 :
    0 ≤ cap12342 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12342 (parameters ⟨0,by decide⟩)
      (scalarRow12342.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12342 ⟨0,by decide⟩ ∧
    (scalarRow12342.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12342 ⟨0,by decide⟩ + (scalarRow12342.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12342.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12342.targetFrame := by
  norm_num [cap12342, scalarRow12342, sourceIndex, cell12342, BstLean.Part263.envelope, parameters]

theorem repair12342Cell1 :
    0 ≤ cap12342 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12342 (parameters ⟨1,by decide⟩)
      (scalarRow12342.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12342 ⟨1,by decide⟩ ∧
    (scalarRow12342.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12342 ⟨1,by decide⟩ + (scalarRow12342.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12342.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12342.targetFrame := by
  norm_num [cap12342, scalarRow12342, sourceIndex, cell12342, BstLean.Part263.envelope, parameters]

theorem repair12342Cell2 :
    0 ≤ cap12342 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12342 (parameters ⟨2,by decide⟩)
      (scalarRow12342.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12342 ⟨2,by decide⟩ ∧
    (scalarRow12342.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12342 ⟨2,by decide⟩ + (scalarRow12342.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12342.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12342.targetFrame := by
  norm_num [cap12342, scalarRow12342, sourceIndex, cell12342, BstLean.Part263.envelope, parameters]

theorem repair12342Cell3 :
    0 ≤ cap12342 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12342 (parameters ⟨3,by decide⟩)
      (scalarRow12342.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12342 ⟨3,by decide⟩ ∧
    (scalarRow12342.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12342 ⟨3,by decide⟩ + (scalarRow12342.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12342.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12342.targetFrame := by
  norm_num [cap12342, scalarRow12342, sourceIndex, cell12342, BstLean.Part263.envelope, parameters]

theorem repair12342Cell4 :
    0 ≤ cap12342 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12342 (parameters ⟨4,by decide⟩)
      (scalarRow12342.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12342 ⟨4,by decide⟩ ∧
    (scalarRow12342.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12342 ⟨4,by decide⟩ + (scalarRow12342.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12342.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12342.targetFrame := by
  norm_num [cap12342, scalarRow12342, sourceIndex, cell12342, BstLean.Part263.envelope, parameters]

theorem repair12342Cell5 :
    0 ≤ cap12342 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12342 (parameters ⟨5,by decide⟩)
      (scalarRow12342.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12342 ⟨5,by decide⟩ ∧
    (scalarRow12342.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12342 ⟨5,by decide⟩ + (scalarRow12342.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12342.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12342.targetFrame := by
  norm_num [cap12342, scalarRow12342, sourceIndex, cell12342, BstLean.Part263.envelope, parameters]

theorem repair12342Cell6 :
    0 ≤ cap12342 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12342 (parameters ⟨6,by decide⟩)
      (scalarRow12342.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12342 ⟨6,by decide⟩ ∧
    (scalarRow12342.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12342 ⟨6,by decide⟩ + (scalarRow12342.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12342.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12342.targetFrame := by
  norm_num [cap12342, scalarRow12342, sourceIndex, cell12342, BstLean.Part263.envelope, parameters]

theorem repair12342Cell7 :
    0 ≤ cap12342 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12342 (parameters ⟨7,by decide⟩)
      (scalarRow12342.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12342 ⟨7,by decide⟩ ∧
    (scalarRow12342.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12342 ⟨7,by decide⟩ + (scalarRow12342.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12342.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12342.targetFrame := by
  norm_num [cap12342, scalarRow12342, sourceIndex, cell12342, BstLean.Part263.envelope, parameters]

theorem repair12342Cell8 :
    0 ≤ cap12342 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12342 (parameters ⟨8,by decide⟩)
      (scalarRow12342.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12342 ⟨8,by decide⟩ ∧
    (scalarRow12342.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12342 ⟨8,by decide⟩ + (scalarRow12342.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12342.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12342.targetFrame := by
  norm_num [cap12342, scalarRow12342, sourceIndex, cell12342, BstLean.Part263.envelope, parameters]

theorem repair12342Cell9 :
    0 ≤ cap12342 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12342 (parameters ⟨9,by decide⟩)
      (scalarRow12342.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12342 ⟨9,by decide⟩ ∧
    (scalarRow12342.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12342 ⟨9,by decide⟩ + (scalarRow12342.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12342.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12342.targetFrame := by
  norm_num [cap12342, scalarRow12342, sourceIndex, cell12342, BstLean.Part263.envelope, parameters]

theorem repair12342Cell10 :
    0 ≤ cap12342 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12342 (parameters ⟨10,by decide⟩)
      (scalarRow12342.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12342 ⟨10,by decide⟩ ∧
    (scalarRow12342.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12342 ⟨10,by decide⟩ + (scalarRow12342.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12342.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12342.targetFrame := by
  norm_num [cap12342, scalarRow12342, sourceIndex, cell12342, BstLean.Part263.envelope, parameters]

theorem repair12342Cell11 :
    0 ≤ cap12342 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12342 (parameters ⟨11,by decide⟩)
      (scalarRow12342.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12342 ⟨11,by decide⟩ ∧
    (scalarRow12342.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12342 ⟨11,by decide⟩ + (scalarRow12342.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12342.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12342.targetFrame := by
  norm_num [cap12342, scalarRow12342, sourceIndex, cell12342, BstLean.Part263.envelope, parameters]

theorem repair12342Cell12 :
    0 ≤ cap12342 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12342 (parameters ⟨12,by decide⟩)
      (scalarRow12342.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12342 ⟨12,by decide⟩ ∧
    (scalarRow12342.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12342 ⟨12,by decide⟩ + (scalarRow12342.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12342.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12342.targetFrame := by
  norm_num [cap12342, scalarRow12342, sourceIndex, cell12342, BstLean.Part263.envelope, parameters]

theorem repair12342Cell13 :
    0 ≤ cap12342 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12342 (parameters ⟨13,by decide⟩)
      (scalarRow12342.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12342 ⟨13,by decide⟩ ∧
    (scalarRow12342.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12342 ⟨13,by decide⟩ + (scalarRow12342.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12342.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12342.targetFrame := by
  norm_num [cap12342, scalarRow12342, sourceIndex, cell12342, BstLean.Part263.envelope, parameters]

theorem repair12342Cell14 :
    0 ≤ cap12342 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12342 (parameters ⟨14,by decide⟩)
      (scalarRow12342.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12342 ⟨14,by decide⟩ ∧
    (scalarRow12342.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12342 ⟨14,by decide⟩ + (scalarRow12342.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12342.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12342.targetFrame := by
  norm_num [cap12342, scalarRow12342, sourceIndex, cell12342, BstLean.Part263.envelope, parameters]

theorem repair12342Cell15 :
    0 ≤ cap12342 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12342 (parameters ⟨15,by decide⟩)
      (scalarRow12342.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12342 ⟨15,by decide⟩ ∧
    (scalarRow12342.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12342 ⟨15,by decide⟩ + (scalarRow12342.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12342.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12342.targetFrame := by
  norm_num [cap12342, scalarRow12342, sourceIndex, cell12342, BstLean.Part263.envelope, parameters]

theorem repair12342Cell16 :
    0 ≤ cap12342 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12342 (parameters ⟨16,by decide⟩)
      (scalarRow12342.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12342 ⟨16,by decide⟩ ∧
    (scalarRow12342.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12342 ⟨16,by decide⟩ + (scalarRow12342.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12342.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12342.targetFrame := by
  norm_num [cap12342, scalarRow12342, sourceIndex, cell12342, BstLean.Part263.envelope, parameters]

theorem repair12342Cell17 :
    0 ≤ cap12342 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12342 (parameters ⟨17,by decide⟩)
      (scalarRow12342.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12342 ⟨17,by decide⟩ ∧
    (scalarRow12342.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12342 ⟨17,by decide⟩ + (scalarRow12342.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12342.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12342.targetFrame := by
  norm_num [cap12342, scalarRow12342, sourceIndex, cell12342, BstLean.Part263.envelope, parameters]

theorem repair12342Cell18 :
    0 ≤ cap12342 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12342 (parameters ⟨18,by decide⟩)
      (scalarRow12342.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12342 ⟨18,by decide⟩ ∧
    (scalarRow12342.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12342 ⟨18,by decide⟩ + (scalarRow12342.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12342.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12342.targetFrame := by
  norm_num [cap12342, scalarRow12342, sourceIndex, cell12342, BstLean.Part263.envelope, parameters]

theorem repair12342Cell19 :
    0 ≤ cap12342 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12342 (parameters ⟨19,by decide⟩)
      (scalarRow12342.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12342 ⟨19,by decide⟩ ∧
    (scalarRow12342.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12342 ⟨19,by decide⟩ + (scalarRow12342.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12342.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12342.targetFrame := by
  norm_num [cap12342, scalarRow12342, sourceIndex, cell12342, BstLean.Part263.envelope, parameters]

theorem repair12342Cell20 :
    0 ≤ cap12342 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12342 (parameters ⟨20,by decide⟩)
      (scalarRow12342.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12342 ⟨20,by decide⟩ ∧
    (scalarRow12342.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12342 ⟨20,by decide⟩ + (scalarRow12342.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12342.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12342.targetFrame := by
  norm_num [cap12342, scalarRow12342, sourceIndex, cell12342, BstLean.Part263.envelope, parameters]

theorem repair12342Cell21 :
    0 ≤ cap12342 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12342 (parameters ⟨21,by decide⟩)
      (scalarRow12342.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12342 ⟨21,by decide⟩ ∧
    (scalarRow12342.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12342 ⟨21,by decide⟩ + (scalarRow12342.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12342.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12342.targetFrame := by
  norm_num [cap12342, scalarRow12342, sourceIndex, cell12342, BstLean.Part263.envelope, parameters]

theorem repair12342Cell22 :
    0 ≤ cap12342 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12342 (parameters ⟨22,by decide⟩)
      (scalarRow12342.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12342 ⟨22,by decide⟩ ∧
    (scalarRow12342.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12342 ⟨22,by decide⟩ + (scalarRow12342.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12342.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12342.targetFrame := by
  norm_num [cap12342, scalarRow12342, sourceIndex, cell12342, BstLean.Part263.envelope, parameters]

theorem repair12342Cell23 :
    0 ≤ cap12342 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12342 (parameters ⟨23,by decide⟩)
      (scalarRow12342.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12342 ⟨23,by decide⟩ ∧
    (scalarRow12342.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12342 ⟨23,by decide⟩ + (scalarRow12342.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12342.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12342.targetFrame := by
  norm_num [cap12342, scalarRow12342, sourceIndex, cell12342, BstLean.Part263.envelope, parameters]

theorem repair12342Cell24 :
    0 ≤ cap12342 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12342 (parameters ⟨24,by decide⟩)
      (scalarRow12342.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12342 ⟨24,by decide⟩ ∧
    (scalarRow12342.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12342 ⟨24,by decide⟩ + (scalarRow12342.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12342.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12342.targetFrame := by
  norm_num [cap12342, scalarRow12342, sourceIndex, cell12342, BstLean.Part263.envelope, parameters]

theorem repair12342Cell25 :
    0 ≤ cap12342 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12342 (parameters ⟨25,by decide⟩)
      (scalarRow12342.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12342 ⟨25,by decide⟩ ∧
    (scalarRow12342.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12342 ⟨25,by decide⟩ + (scalarRow12342.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12342.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12342.targetFrame := by
  norm_num [cap12342, scalarRow12342, sourceIndex, cell12342, BstLean.Part263.envelope, parameters]

theorem repair12342Cell26 :
    0 ≤ cap12342 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12342 (parameters ⟨26,by decide⟩)
      (scalarRow12342.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12342 ⟨26,by decide⟩ ∧
    (scalarRow12342.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12342 ⟨26,by decide⟩ + (scalarRow12342.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12342.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12342.targetFrame := by
  norm_num [cap12342, scalarRow12342, sourceIndex, cell12342, BstLean.Part263.envelope, parameters]

theorem repair12342Cell27 :
    0 ≤ cap12342 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12342 (parameters ⟨27,by decide⟩)
      (scalarRow12342.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12342 ⟨27,by decide⟩ ∧
    (scalarRow12342.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12342 ⟨27,by decide⟩ + (scalarRow12342.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12342.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12342.targetFrame := by
  norm_num [cap12342, scalarRow12342, sourceIndex, cell12342, BstLean.Part263.envelope, parameters]

theorem repair12342Cell28 :
    0 ≤ cap12342 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12342 (parameters ⟨28,by decide⟩)
      (scalarRow12342.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12342 ⟨28,by decide⟩ ∧
    (scalarRow12342.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12342 ⟨28,by decide⟩ + (scalarRow12342.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12342.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12342.targetFrame := by
  norm_num [cap12342, scalarRow12342, sourceIndex, cell12342, BstLean.Part263.envelope, parameters]

theorem repair12342Cell29 :
    0 ≤ cap12342 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12342 (parameters ⟨29,by decide⟩)
      (scalarRow12342.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12342 ⟨29,by decide⟩ ∧
    (scalarRow12342.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12342 ⟨29,by decide⟩ + (scalarRow12342.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12342.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12342.targetFrame := by
  norm_num [cap12342, scalarRow12342, sourceIndex, cell12342, BstLean.Part263.envelope, parameters]

theorem repair12342Cell30 :
    0 ≤ cap12342 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12342 (parameters ⟨30,by decide⟩)
      (scalarRow12342.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12342 ⟨30,by decide⟩ ∧
    (scalarRow12342.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12342 ⟨30,by decide⟩ + (scalarRow12342.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12342.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12342.targetFrame := by
  norm_num [cap12342, scalarRow12342, sourceIndex, cell12342, BstLean.Part263.envelope, parameters]

theorem repair12342Cell31 :
    0 ≤ cap12342 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12342 (parameters ⟨31,by decide⟩)
      (scalarRow12342.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12342 ⟨31,by decide⟩ ∧
    (scalarRow12342.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12342 ⟨31,by decide⟩ + (scalarRow12342.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12342.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12342.targetFrame := by
  norm_num [cap12342, scalarRow12342, sourceIndex, cell12342, BstLean.Part263.envelope, parameters]

theorem repair12342Cell32 :
    0 ≤ cap12342 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12342 (parameters ⟨32,by decide⟩)
      (scalarRow12342.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12342 ⟨32,by decide⟩ ∧
    (scalarRow12342.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12342 ⟨32,by decide⟩ + (scalarRow12342.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12342.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12342.targetFrame := by
  norm_num [cap12342, scalarRow12342, sourceIndex, cell12342, BstLean.Part263.envelope, parameters]

theorem repair12342Cell33 :
    0 ≤ cap12342 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12342 (parameters ⟨33,by decide⟩)
      (scalarRow12342.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12342 ⟨33,by decide⟩ ∧
    (scalarRow12342.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12342 ⟨33,by decide⟩ + (scalarRow12342.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12342.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12342.targetFrame := by
  norm_num [cap12342, scalarRow12342, sourceIndex, cell12342, BstLean.Part263.envelope, parameters]

theorem repair12342Cell34 :
    0 ≤ cap12342 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12342 (parameters ⟨34,by decide⟩)
      (scalarRow12342.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12342 ⟨34,by decide⟩ ∧
    (scalarRow12342.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12342 ⟨34,by decide⟩ + (scalarRow12342.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12342.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12342.targetFrame := by
  norm_num [cap12342, scalarRow12342, sourceIndex, cell12342, BstLean.Part263.envelope, parameters]

theorem repair12342Cell35 :
    0 ≤ cap12342 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12342 (parameters ⟨35,by decide⟩)
      (scalarRow12342.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12342 ⟨35,by decide⟩ ∧
    (scalarRow12342.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12342 ⟨35,by decide⟩ + (scalarRow12342.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12342.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12342.targetFrame := by
  norm_num [cap12342, scalarRow12342, sourceIndex, cell12342, BstLean.Part263.envelope, parameters]

theorem repair12342Cell36 :
    0 ≤ cap12342 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12342 (parameters ⟨36,by decide⟩)
      (scalarRow12342.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12342 ⟨36,by decide⟩ ∧
    (scalarRow12342.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12342 ⟨36,by decide⟩ + (scalarRow12342.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12342.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12342.targetFrame := by
  norm_num [cap12342, scalarRow12342, sourceIndex, cell12342, BstLean.Part263.envelope, parameters]

theorem repair12342Cell37 :
    0 ≤ cap12342 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12342 (parameters ⟨37,by decide⟩)
      (scalarRow12342.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12342 ⟨37,by decide⟩ ∧
    (scalarRow12342.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12342 ⟨37,by decide⟩ + (scalarRow12342.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12342.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12342.targetFrame := by
  norm_num [cap12342, scalarRow12342, sourceIndex, cell12342, BstLean.Part263.envelope, parameters]

theorem repair12342Cell38 :
    0 ≤ cap12342 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12342 (parameters ⟨38,by decide⟩)
      (scalarRow12342.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12342 ⟨38,by decide⟩ ∧
    (scalarRow12342.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12342 ⟨38,by decide⟩ + (scalarRow12342.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12342.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12342.targetFrame := by
  norm_num [cap12342, scalarRow12342, sourceIndex, cell12342, BstLean.Part263.envelope, parameters]

theorem repair12342Cell39 :
    0 ≤ cap12342 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12342 (parameters ⟨39,by decide⟩)
      (scalarRow12342.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12342 ⟨39,by decide⟩ ∧
    (scalarRow12342.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12342 ⟨39,by decide⟩ + (scalarRow12342.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12342.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12342.targetFrame := by
  norm_num [cap12342, scalarRow12342, sourceIndex, cell12342, BstLean.Part263.envelope, parameters]

theorem repair12342Cell40 :
    0 ≤ cap12342 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12342 (parameters ⟨40,by decide⟩)
      (scalarRow12342.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12342 ⟨40,by decide⟩ ∧
    (scalarRow12342.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12342 ⟨40,by decide⟩ + (scalarRow12342.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12342.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12342.targetFrame := by
  norm_num [cap12342, scalarRow12342, sourceIndex, cell12342, BstLean.Part263.envelope, parameters]

theorem repair12342Cell41 :
    0 ≤ cap12342 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12342 (parameters ⟨41,by decide⟩)
      (scalarRow12342.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12342 ⟨41,by decide⟩ ∧
    (scalarRow12342.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12342 ⟨41,by decide⟩ + (scalarRow12342.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12342.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12342.targetFrame := by
  norm_num [cap12342, scalarRow12342, sourceIndex, cell12342, BstLean.Part263.envelope, parameters]

theorem repair12342Cell42 :
    0 ≤ cap12342 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12342 (parameters ⟨42,by decide⟩)
      (scalarRow12342.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12342 ⟨42,by decide⟩ ∧
    (scalarRow12342.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12342 ⟨42,by decide⟩ + (scalarRow12342.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12342.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12342.targetFrame := by
  norm_num [cap12342, scalarRow12342, sourceIndex, cell12342, BstLean.Part263.envelope, parameters]

theorem repair12342Cells (j : Fin 43) :
    0 ≤ cap12342 j ∧
    BstLean.Part263.envelope 12342 (parameters j) (scalarRow12342.table (sourceIndex j)).upper ≤ cap12342 j ∧
    (scalarRow12342.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12342 j + (scalarRow12342.table (sourceIndex j)).centre) /
      (scalarRow12342.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12342.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12342Cell0
  | ⟨1,_⟩ => exact repair12342Cell1
  | ⟨2,_⟩ => exact repair12342Cell2
  | ⟨3,_⟩ => exact repair12342Cell3
  | ⟨4,_⟩ => exact repair12342Cell4
  | ⟨5,_⟩ => exact repair12342Cell5
  | ⟨6,_⟩ => exact repair12342Cell6
  | ⟨7,_⟩ => exact repair12342Cell7
  | ⟨8,_⟩ => exact repair12342Cell8
  | ⟨9,_⟩ => exact repair12342Cell9
  | ⟨10,_⟩ => exact repair12342Cell10
  | ⟨11,_⟩ => exact repair12342Cell11
  | ⟨12,_⟩ => exact repair12342Cell12
  | ⟨13,_⟩ => exact repair12342Cell13
  | ⟨14,_⟩ => exact repair12342Cell14
  | ⟨15,_⟩ => exact repair12342Cell15
  | ⟨16,_⟩ => exact repair12342Cell16
  | ⟨17,_⟩ => exact repair12342Cell17
  | ⟨18,_⟩ => exact repair12342Cell18
  | ⟨19,_⟩ => exact repair12342Cell19
  | ⟨20,_⟩ => exact repair12342Cell20
  | ⟨21,_⟩ => exact repair12342Cell21
  | ⟨22,_⟩ => exact repair12342Cell22
  | ⟨23,_⟩ => exact repair12342Cell23
  | ⟨24,_⟩ => exact repair12342Cell24
  | ⟨25,_⟩ => exact repair12342Cell25
  | ⟨26,_⟩ => exact repair12342Cell26
  | ⟨27,_⟩ => exact repair12342Cell27
  | ⟨28,_⟩ => exact repair12342Cell28
  | ⟨29,_⟩ => exact repair12342Cell29
  | ⟨30,_⟩ => exact repair12342Cell30
  | ⟨31,_⟩ => exact repair12342Cell31
  | ⟨32,_⟩ => exact repair12342Cell32
  | ⟨33,_⟩ => exact repair12342Cell33
  | ⟨34,_⟩ => exact repair12342Cell34
  | ⟨35,_⟩ => exact repair12342Cell35
  | ⟨36,_⟩ => exact repair12342Cell36
  | ⟨37,_⟩ => exact repair12342Cell37
  | ⟨38,_⟩ => exact repair12342Cell38
  | ⟨39,_⟩ => exact repair12342Cell39
  | ⟨40,_⟩ => exact repair12342Cell40
  | ⟨41,_⟩ => exact repair12342Cell41
  | ⟨42,_⟩ => exact repair12342Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12342 : FrameRepair 12342 scalarRow12342 where
  cap := cap12342
  cap_nonneg := fun j => (repair12342Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12342])
  endpoint := fun j => (repair12342Cells j).2.1
  endpoint_upper := fun j => (repair12342Cells j).2.2.1
  frame := fun j => (repair12342Cells j).2.2.2

noncomputable def cap12343 : Fin 43 → ℝ
  | ⟨0,_⟩ => (275943827 / 1000000000 : ℝ)
  | ⟨1,_⟩ => (138173167 / 500000000 : ℝ)
  | ⟨2,_⟩ => (34593481 / 125000000 : ℝ)
  | ⟨3,_⟩ => (55429673 / 200000000 : ℝ)
  | ⟨4,_⟩ => (277547893 / 1000000000 : ℝ)
  | ⟨5,_⟩ => (277946431 / 1000000000 : ℝ)
  | ⟨6,_⟩ => (278343509 / 1000000000 : ℝ)
  | ⟨7,_⟩ => (139370041 / 500000000 : ℝ)
  | ⟨8,_⟩ => (279135679 / 1000000000 : ℝ)
  | ⟨9,_⟩ => (55906061 / 200000000 : ℝ)
  | ⟨10,_⟩ => (279923961 / 1000000000 : ℝ)
  | ⟨11,_⟩ => (280316169 / 1000000000 : ℝ)
  | ⟨12,_⟩ => (280707901 / 1000000000 : ℝ)
  | ⟨13,_⟩ => (140549093 / 500000000 : ℝ)
  | ⟨14,_⟩ => (70372101 / 250000000 : ℝ)
  | ⟨15,_⟩ => (281877523 / 1000000000 : ℝ)
  | ⟨16,_⟩ => (282265701 / 1000000000 : ℝ)
  | ⟨17,_⟩ => (70663237 / 250000000 : ℝ)
  | ⟨18,_⟩ => (35379907 / 125000000 : ℝ)
  | ⟨19,_⟩ => (70856159 / 250000000 : ℝ)
  | ⟨20,_⟩ => (28380909 / 100000000 : ℝ)
  | ⟨21,_⟩ => (71048157 / 250000000 : ℝ)
  | ⟨22,_⟩ => (284575243 / 1000000000 : ℝ)
  | ⟨23,_⟩ => (8904889 / 31250000 : ℝ)
  | ⟨24,_⟩ => (285337241 / 1000000000 : ℝ)
  | ⟨25,_⟩ => (285716673 / 1000000000 : ℝ)
  | ⟨26,_⟩ => (143047851 / 500000000 : ℝ)
  | ⟨27,_⟩ => (71618333 / 250000000 : ℝ)
  | ⟨28,_⟩ => (143425033 / 500000000 : ℝ)
  | ⟨29,_⟩ => (57445181 / 200000000 : ℝ)
  | ⟨30,_⟩ => (287600351 / 1000000000 : ℝ)
  | ⟨31,_⟩ => (287974413 / 1000000000 : ℝ)
  | ⟨32,_⟩ => (72086899 / 250000000 : ℝ)
  | ⟨33,_⟩ => (72179847 / 250000000 : ℝ)
  | ⟨34,_⟩ => (289090307 / 1000000000 : ℝ)
  | ⟨35,_⟩ => (144730177 / 500000000 : ℝ)
  | ⟨36,_⟩ => (11593181 / 40000000 : ℝ)
  | ⟨37,_⟩ => (290197837 / 1000000000 : ℝ)
  | ⟨38,_⟩ => (58113057 / 200000000 : ℝ)
  | ⟨39,_⟩ => (145465681 / 500000000 : ℝ)
  | ⟨40,_⟩ => (14564829 / 50000000 : ℝ)
  | ⟨41,_⟩ => (291660947 / 1000000000 : ℝ)
  | ⟨42,_⟩ => (292024463 / 1000000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12343Cell0 :
    0 ≤ cap12343 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12343 (parameters ⟨0,by decide⟩)
      (scalarRow12343.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12343 ⟨0,by decide⟩ ∧
    (scalarRow12343.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12343 ⟨0,by decide⟩ + (scalarRow12343.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12343.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12343.targetFrame := by
  norm_num [cap12343, scalarRow12343, sourceIndex, cell12343, BstLean.Part263.envelope, parameters]

theorem repair12343Cell1 :
    0 ≤ cap12343 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12343 (parameters ⟨1,by decide⟩)
      (scalarRow12343.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12343 ⟨1,by decide⟩ ∧
    (scalarRow12343.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12343 ⟨1,by decide⟩ + (scalarRow12343.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12343.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12343.targetFrame := by
  norm_num [cap12343, scalarRow12343, sourceIndex, cell12343, BstLean.Part263.envelope, parameters]

theorem repair12343Cell2 :
    0 ≤ cap12343 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12343 (parameters ⟨2,by decide⟩)
      (scalarRow12343.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12343 ⟨2,by decide⟩ ∧
    (scalarRow12343.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12343 ⟨2,by decide⟩ + (scalarRow12343.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12343.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12343.targetFrame := by
  norm_num [cap12343, scalarRow12343, sourceIndex, cell12343, BstLean.Part263.envelope, parameters]

theorem repair12343Cell3 :
    0 ≤ cap12343 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12343 (parameters ⟨3,by decide⟩)
      (scalarRow12343.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12343 ⟨3,by decide⟩ ∧
    (scalarRow12343.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12343 ⟨3,by decide⟩ + (scalarRow12343.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12343.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12343.targetFrame := by
  norm_num [cap12343, scalarRow12343, sourceIndex, cell12343, BstLean.Part263.envelope, parameters]

theorem repair12343Cell4 :
    0 ≤ cap12343 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12343 (parameters ⟨4,by decide⟩)
      (scalarRow12343.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12343 ⟨4,by decide⟩ ∧
    (scalarRow12343.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12343 ⟨4,by decide⟩ + (scalarRow12343.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12343.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12343.targetFrame := by
  norm_num [cap12343, scalarRow12343, sourceIndex, cell12343, BstLean.Part263.envelope, parameters]

theorem repair12343Cell5 :
    0 ≤ cap12343 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12343 (parameters ⟨5,by decide⟩)
      (scalarRow12343.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12343 ⟨5,by decide⟩ ∧
    (scalarRow12343.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12343 ⟨5,by decide⟩ + (scalarRow12343.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12343.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12343.targetFrame := by
  norm_num [cap12343, scalarRow12343, sourceIndex, cell12343, BstLean.Part263.envelope, parameters]

theorem repair12343Cell6 :
    0 ≤ cap12343 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12343 (parameters ⟨6,by decide⟩)
      (scalarRow12343.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12343 ⟨6,by decide⟩ ∧
    (scalarRow12343.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12343 ⟨6,by decide⟩ + (scalarRow12343.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12343.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12343.targetFrame := by
  norm_num [cap12343, scalarRow12343, sourceIndex, cell12343, BstLean.Part263.envelope, parameters]

theorem repair12343Cell7 :
    0 ≤ cap12343 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12343 (parameters ⟨7,by decide⟩)
      (scalarRow12343.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12343 ⟨7,by decide⟩ ∧
    (scalarRow12343.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12343 ⟨7,by decide⟩ + (scalarRow12343.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12343.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12343.targetFrame := by
  norm_num [cap12343, scalarRow12343, sourceIndex, cell12343, BstLean.Part263.envelope, parameters]

theorem repair12343Cell8 :
    0 ≤ cap12343 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12343 (parameters ⟨8,by decide⟩)
      (scalarRow12343.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12343 ⟨8,by decide⟩ ∧
    (scalarRow12343.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12343 ⟨8,by decide⟩ + (scalarRow12343.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12343.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12343.targetFrame := by
  norm_num [cap12343, scalarRow12343, sourceIndex, cell12343, BstLean.Part263.envelope, parameters]

theorem repair12343Cell9 :
    0 ≤ cap12343 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12343 (parameters ⟨9,by decide⟩)
      (scalarRow12343.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12343 ⟨9,by decide⟩ ∧
    (scalarRow12343.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12343 ⟨9,by decide⟩ + (scalarRow12343.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12343.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12343.targetFrame := by
  norm_num [cap12343, scalarRow12343, sourceIndex, cell12343, BstLean.Part263.envelope, parameters]

theorem repair12343Cell10 :
    0 ≤ cap12343 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12343 (parameters ⟨10,by decide⟩)
      (scalarRow12343.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12343 ⟨10,by decide⟩ ∧
    (scalarRow12343.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12343 ⟨10,by decide⟩ + (scalarRow12343.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12343.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12343.targetFrame := by
  norm_num [cap12343, scalarRow12343, sourceIndex, cell12343, BstLean.Part263.envelope, parameters]

theorem repair12343Cell11 :
    0 ≤ cap12343 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12343 (parameters ⟨11,by decide⟩)
      (scalarRow12343.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12343 ⟨11,by decide⟩ ∧
    (scalarRow12343.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12343 ⟨11,by decide⟩ + (scalarRow12343.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12343.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12343.targetFrame := by
  norm_num [cap12343, scalarRow12343, sourceIndex, cell12343, BstLean.Part263.envelope, parameters]

theorem repair12343Cell12 :
    0 ≤ cap12343 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12343 (parameters ⟨12,by decide⟩)
      (scalarRow12343.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12343 ⟨12,by decide⟩ ∧
    (scalarRow12343.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12343 ⟨12,by decide⟩ + (scalarRow12343.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12343.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12343.targetFrame := by
  norm_num [cap12343, scalarRow12343, sourceIndex, cell12343, BstLean.Part263.envelope, parameters]

theorem repair12343Cell13 :
    0 ≤ cap12343 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12343 (parameters ⟨13,by decide⟩)
      (scalarRow12343.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12343 ⟨13,by decide⟩ ∧
    (scalarRow12343.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12343 ⟨13,by decide⟩ + (scalarRow12343.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12343.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12343.targetFrame := by
  norm_num [cap12343, scalarRow12343, sourceIndex, cell12343, BstLean.Part263.envelope, parameters]

theorem repair12343Cell14 :
    0 ≤ cap12343 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12343 (parameters ⟨14,by decide⟩)
      (scalarRow12343.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12343 ⟨14,by decide⟩ ∧
    (scalarRow12343.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12343 ⟨14,by decide⟩ + (scalarRow12343.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12343.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12343.targetFrame := by
  norm_num [cap12343, scalarRow12343, sourceIndex, cell12343, BstLean.Part263.envelope, parameters]

theorem repair12343Cell15 :
    0 ≤ cap12343 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12343 (parameters ⟨15,by decide⟩)
      (scalarRow12343.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12343 ⟨15,by decide⟩ ∧
    (scalarRow12343.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12343 ⟨15,by decide⟩ + (scalarRow12343.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12343.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12343.targetFrame := by
  norm_num [cap12343, scalarRow12343, sourceIndex, cell12343, BstLean.Part263.envelope, parameters]

theorem repair12343Cell16 :
    0 ≤ cap12343 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12343 (parameters ⟨16,by decide⟩)
      (scalarRow12343.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12343 ⟨16,by decide⟩ ∧
    (scalarRow12343.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12343 ⟨16,by decide⟩ + (scalarRow12343.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12343.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12343.targetFrame := by
  norm_num [cap12343, scalarRow12343, sourceIndex, cell12343, BstLean.Part263.envelope, parameters]

theorem repair12343Cell17 :
    0 ≤ cap12343 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12343 (parameters ⟨17,by decide⟩)
      (scalarRow12343.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12343 ⟨17,by decide⟩ ∧
    (scalarRow12343.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12343 ⟨17,by decide⟩ + (scalarRow12343.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12343.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12343.targetFrame := by
  norm_num [cap12343, scalarRow12343, sourceIndex, cell12343, BstLean.Part263.envelope, parameters]

theorem repair12343Cell18 :
    0 ≤ cap12343 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12343 (parameters ⟨18,by decide⟩)
      (scalarRow12343.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12343 ⟨18,by decide⟩ ∧
    (scalarRow12343.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12343 ⟨18,by decide⟩ + (scalarRow12343.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12343.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12343.targetFrame := by
  norm_num [cap12343, scalarRow12343, sourceIndex, cell12343, BstLean.Part263.envelope, parameters]

theorem repair12343Cell19 :
    0 ≤ cap12343 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12343 (parameters ⟨19,by decide⟩)
      (scalarRow12343.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12343 ⟨19,by decide⟩ ∧
    (scalarRow12343.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12343 ⟨19,by decide⟩ + (scalarRow12343.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12343.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12343.targetFrame := by
  norm_num [cap12343, scalarRow12343, sourceIndex, cell12343, BstLean.Part263.envelope, parameters]

theorem repair12343Cell20 :
    0 ≤ cap12343 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12343 (parameters ⟨20,by decide⟩)
      (scalarRow12343.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12343 ⟨20,by decide⟩ ∧
    (scalarRow12343.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12343 ⟨20,by decide⟩ + (scalarRow12343.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12343.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12343.targetFrame := by
  norm_num [cap12343, scalarRow12343, sourceIndex, cell12343, BstLean.Part263.envelope, parameters]

theorem repair12343Cell21 :
    0 ≤ cap12343 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12343 (parameters ⟨21,by decide⟩)
      (scalarRow12343.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12343 ⟨21,by decide⟩ ∧
    (scalarRow12343.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12343 ⟨21,by decide⟩ + (scalarRow12343.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12343.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12343.targetFrame := by
  norm_num [cap12343, scalarRow12343, sourceIndex, cell12343, BstLean.Part263.envelope, parameters]

theorem repair12343Cell22 :
    0 ≤ cap12343 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12343 (parameters ⟨22,by decide⟩)
      (scalarRow12343.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12343 ⟨22,by decide⟩ ∧
    (scalarRow12343.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12343 ⟨22,by decide⟩ + (scalarRow12343.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12343.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12343.targetFrame := by
  norm_num [cap12343, scalarRow12343, sourceIndex, cell12343, BstLean.Part263.envelope, parameters]

theorem repair12343Cell23 :
    0 ≤ cap12343 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12343 (parameters ⟨23,by decide⟩)
      (scalarRow12343.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12343 ⟨23,by decide⟩ ∧
    (scalarRow12343.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12343 ⟨23,by decide⟩ + (scalarRow12343.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12343.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12343.targetFrame := by
  norm_num [cap12343, scalarRow12343, sourceIndex, cell12343, BstLean.Part263.envelope, parameters]

theorem repair12343Cell24 :
    0 ≤ cap12343 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12343 (parameters ⟨24,by decide⟩)
      (scalarRow12343.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12343 ⟨24,by decide⟩ ∧
    (scalarRow12343.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12343 ⟨24,by decide⟩ + (scalarRow12343.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12343.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12343.targetFrame := by
  norm_num [cap12343, scalarRow12343, sourceIndex, cell12343, BstLean.Part263.envelope, parameters]

theorem repair12343Cell25 :
    0 ≤ cap12343 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12343 (parameters ⟨25,by decide⟩)
      (scalarRow12343.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12343 ⟨25,by decide⟩ ∧
    (scalarRow12343.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12343 ⟨25,by decide⟩ + (scalarRow12343.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12343.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12343.targetFrame := by
  norm_num [cap12343, scalarRow12343, sourceIndex, cell12343, BstLean.Part263.envelope, parameters]

theorem repair12343Cell26 :
    0 ≤ cap12343 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12343 (parameters ⟨26,by decide⟩)
      (scalarRow12343.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12343 ⟨26,by decide⟩ ∧
    (scalarRow12343.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12343 ⟨26,by decide⟩ + (scalarRow12343.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12343.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12343.targetFrame := by
  norm_num [cap12343, scalarRow12343, sourceIndex, cell12343, BstLean.Part263.envelope, parameters]

theorem repair12343Cell27 :
    0 ≤ cap12343 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12343 (parameters ⟨27,by decide⟩)
      (scalarRow12343.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12343 ⟨27,by decide⟩ ∧
    (scalarRow12343.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12343 ⟨27,by decide⟩ + (scalarRow12343.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12343.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12343.targetFrame := by
  norm_num [cap12343, scalarRow12343, sourceIndex, cell12343, BstLean.Part263.envelope, parameters]

theorem repair12343Cell28 :
    0 ≤ cap12343 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12343 (parameters ⟨28,by decide⟩)
      (scalarRow12343.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12343 ⟨28,by decide⟩ ∧
    (scalarRow12343.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12343 ⟨28,by decide⟩ + (scalarRow12343.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12343.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12343.targetFrame := by
  norm_num [cap12343, scalarRow12343, sourceIndex, cell12343, BstLean.Part263.envelope, parameters]

theorem repair12343Cell29 :
    0 ≤ cap12343 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12343 (parameters ⟨29,by decide⟩)
      (scalarRow12343.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12343 ⟨29,by decide⟩ ∧
    (scalarRow12343.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12343 ⟨29,by decide⟩ + (scalarRow12343.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12343.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12343.targetFrame := by
  norm_num [cap12343, scalarRow12343, sourceIndex, cell12343, BstLean.Part263.envelope, parameters]

theorem repair12343Cell30 :
    0 ≤ cap12343 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12343 (parameters ⟨30,by decide⟩)
      (scalarRow12343.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12343 ⟨30,by decide⟩ ∧
    (scalarRow12343.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12343 ⟨30,by decide⟩ + (scalarRow12343.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12343.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12343.targetFrame := by
  norm_num [cap12343, scalarRow12343, sourceIndex, cell12343, BstLean.Part263.envelope, parameters]

theorem repair12343Cell31 :
    0 ≤ cap12343 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12343 (parameters ⟨31,by decide⟩)
      (scalarRow12343.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12343 ⟨31,by decide⟩ ∧
    (scalarRow12343.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12343 ⟨31,by decide⟩ + (scalarRow12343.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12343.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12343.targetFrame := by
  norm_num [cap12343, scalarRow12343, sourceIndex, cell12343, BstLean.Part263.envelope, parameters]

theorem repair12343Cell32 :
    0 ≤ cap12343 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12343 (parameters ⟨32,by decide⟩)
      (scalarRow12343.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12343 ⟨32,by decide⟩ ∧
    (scalarRow12343.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12343 ⟨32,by decide⟩ + (scalarRow12343.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12343.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12343.targetFrame := by
  norm_num [cap12343, scalarRow12343, sourceIndex, cell12343, BstLean.Part263.envelope, parameters]

theorem repair12343Cell33 :
    0 ≤ cap12343 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12343 (parameters ⟨33,by decide⟩)
      (scalarRow12343.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12343 ⟨33,by decide⟩ ∧
    (scalarRow12343.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12343 ⟨33,by decide⟩ + (scalarRow12343.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12343.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12343.targetFrame := by
  norm_num [cap12343, scalarRow12343, sourceIndex, cell12343, BstLean.Part263.envelope, parameters]

theorem repair12343Cell34 :
    0 ≤ cap12343 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12343 (parameters ⟨34,by decide⟩)
      (scalarRow12343.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12343 ⟨34,by decide⟩ ∧
    (scalarRow12343.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12343 ⟨34,by decide⟩ + (scalarRow12343.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12343.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12343.targetFrame := by
  norm_num [cap12343, scalarRow12343, sourceIndex, cell12343, BstLean.Part263.envelope, parameters]

theorem repair12343Cell35 :
    0 ≤ cap12343 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12343 (parameters ⟨35,by decide⟩)
      (scalarRow12343.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12343 ⟨35,by decide⟩ ∧
    (scalarRow12343.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12343 ⟨35,by decide⟩ + (scalarRow12343.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12343.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12343.targetFrame := by
  norm_num [cap12343, scalarRow12343, sourceIndex, cell12343, BstLean.Part263.envelope, parameters]

theorem repair12343Cell36 :
    0 ≤ cap12343 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12343 (parameters ⟨36,by decide⟩)
      (scalarRow12343.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12343 ⟨36,by decide⟩ ∧
    (scalarRow12343.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12343 ⟨36,by decide⟩ + (scalarRow12343.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12343.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12343.targetFrame := by
  norm_num [cap12343, scalarRow12343, sourceIndex, cell12343, BstLean.Part263.envelope, parameters]

theorem repair12343Cell37 :
    0 ≤ cap12343 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12343 (parameters ⟨37,by decide⟩)
      (scalarRow12343.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12343 ⟨37,by decide⟩ ∧
    (scalarRow12343.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12343 ⟨37,by decide⟩ + (scalarRow12343.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12343.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12343.targetFrame := by
  norm_num [cap12343, scalarRow12343, sourceIndex, cell12343, BstLean.Part263.envelope, parameters]

theorem repair12343Cell38 :
    0 ≤ cap12343 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12343 (parameters ⟨38,by decide⟩)
      (scalarRow12343.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12343 ⟨38,by decide⟩ ∧
    (scalarRow12343.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12343 ⟨38,by decide⟩ + (scalarRow12343.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12343.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12343.targetFrame := by
  norm_num [cap12343, scalarRow12343, sourceIndex, cell12343, BstLean.Part263.envelope, parameters]

theorem repair12343Cell39 :
    0 ≤ cap12343 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12343 (parameters ⟨39,by decide⟩)
      (scalarRow12343.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12343 ⟨39,by decide⟩ ∧
    (scalarRow12343.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12343 ⟨39,by decide⟩ + (scalarRow12343.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12343.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12343.targetFrame := by
  norm_num [cap12343, scalarRow12343, sourceIndex, cell12343, BstLean.Part263.envelope, parameters]

theorem repair12343Cell40 :
    0 ≤ cap12343 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12343 (parameters ⟨40,by decide⟩)
      (scalarRow12343.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12343 ⟨40,by decide⟩ ∧
    (scalarRow12343.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12343 ⟨40,by decide⟩ + (scalarRow12343.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12343.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12343.targetFrame := by
  norm_num [cap12343, scalarRow12343, sourceIndex, cell12343, BstLean.Part263.envelope, parameters]

theorem repair12343Cell41 :
    0 ≤ cap12343 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12343 (parameters ⟨41,by decide⟩)
      (scalarRow12343.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12343 ⟨41,by decide⟩ ∧
    (scalarRow12343.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12343 ⟨41,by decide⟩ + (scalarRow12343.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12343.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12343.targetFrame := by
  norm_num [cap12343, scalarRow12343, sourceIndex, cell12343, BstLean.Part263.envelope, parameters]

theorem repair12343Cell42 :
    0 ≤ cap12343 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12343 (parameters ⟨42,by decide⟩)
      (scalarRow12343.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12343 ⟨42,by decide⟩ ∧
    (scalarRow12343.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12343 ⟨42,by decide⟩ + (scalarRow12343.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12343.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12343.targetFrame := by
  norm_num [cap12343, scalarRow12343, sourceIndex, cell12343, BstLean.Part263.envelope, parameters]

theorem repair12343Cells (j : Fin 43) :
    0 ≤ cap12343 j ∧
    BstLean.Part263.envelope 12343 (parameters j) (scalarRow12343.table (sourceIndex j)).upper ≤ cap12343 j ∧
    (scalarRow12343.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12343 j + (scalarRow12343.table (sourceIndex j)).centre) /
      (scalarRow12343.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12343.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12343Cell0
  | ⟨1,_⟩ => exact repair12343Cell1
  | ⟨2,_⟩ => exact repair12343Cell2
  | ⟨3,_⟩ => exact repair12343Cell3
  | ⟨4,_⟩ => exact repair12343Cell4
  | ⟨5,_⟩ => exact repair12343Cell5
  | ⟨6,_⟩ => exact repair12343Cell6
  | ⟨7,_⟩ => exact repair12343Cell7
  | ⟨8,_⟩ => exact repair12343Cell8
  | ⟨9,_⟩ => exact repair12343Cell9
  | ⟨10,_⟩ => exact repair12343Cell10
  | ⟨11,_⟩ => exact repair12343Cell11
  | ⟨12,_⟩ => exact repair12343Cell12
  | ⟨13,_⟩ => exact repair12343Cell13
  | ⟨14,_⟩ => exact repair12343Cell14
  | ⟨15,_⟩ => exact repair12343Cell15
  | ⟨16,_⟩ => exact repair12343Cell16
  | ⟨17,_⟩ => exact repair12343Cell17
  | ⟨18,_⟩ => exact repair12343Cell18
  | ⟨19,_⟩ => exact repair12343Cell19
  | ⟨20,_⟩ => exact repair12343Cell20
  | ⟨21,_⟩ => exact repair12343Cell21
  | ⟨22,_⟩ => exact repair12343Cell22
  | ⟨23,_⟩ => exact repair12343Cell23
  | ⟨24,_⟩ => exact repair12343Cell24
  | ⟨25,_⟩ => exact repair12343Cell25
  | ⟨26,_⟩ => exact repair12343Cell26
  | ⟨27,_⟩ => exact repair12343Cell27
  | ⟨28,_⟩ => exact repair12343Cell28
  | ⟨29,_⟩ => exact repair12343Cell29
  | ⟨30,_⟩ => exact repair12343Cell30
  | ⟨31,_⟩ => exact repair12343Cell31
  | ⟨32,_⟩ => exact repair12343Cell32
  | ⟨33,_⟩ => exact repair12343Cell33
  | ⟨34,_⟩ => exact repair12343Cell34
  | ⟨35,_⟩ => exact repair12343Cell35
  | ⟨36,_⟩ => exact repair12343Cell36
  | ⟨37,_⟩ => exact repair12343Cell37
  | ⟨38,_⟩ => exact repair12343Cell38
  | ⟨39,_⟩ => exact repair12343Cell39
  | ⟨40,_⟩ => exact repair12343Cell40
  | ⟨41,_⟩ => exact repair12343Cell41
  | ⟨42,_⟩ => exact repair12343Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12343 : FrameRepair 12343 scalarRow12343 where
  cap := cap12343
  cap_nonneg := fun j => (repair12343Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12343])
  endpoint := fun j => (repair12343Cells j).2.1
  endpoint_upper := fun j => (repair12343Cells j).2.2.1
  frame := fun j => (repair12343Cells j).2.2.2

noncomputable def cap12344 : Fin 43 → ℝ
  | ⟨0,_⟩ => (34492969 / 125000000 : ℝ)
  | ⟨1,_⟩ => (276346253 / 1000000000 : ℝ)
  | ⟨2,_⟩ => (3459347 / 12500000 : ℝ)
  | ⟨3,_⟩ => (277148271 / 1000000000 : ℝ)
  | ⟨4,_⟩ => (17346737 / 62500000 : ℝ)
  | ⟨5,_⟩ => (69486581 / 250000000 : ℝ)
  | ⟨6,_⟩ => (69585849 / 250000000 : ℝ)
  | ⟨7,_⟩ => (139369981 / 500000000 : ℝ)
  | ⟨8,_⟩ => (279135553 / 1000000000 : ℝ)
  | ⟨9,_⟩ => (279530173 / 1000000000 : ℝ)
  | ⟨10,_⟩ => (279923823 / 1000000000 : ℝ)
  | ⟨11,_⟩ => (35039503 / 125000000 : ℝ)
  | ⟨12,_⟩ => (280707749 / 1000000000 : ℝ)
  | ⟨13,_⟩ => (70274507 / 250000000 : ℝ)
  | ⟨14,_⟩ => (3518603 / 12500000 : ℝ)
  | ⟨15,_⟩ => (281877353 / 1000000000 : ℝ)
  | ⟨16,_⟩ => (11290621 / 40000000 : ℝ)
  | ⟨17,_⟩ => (56530553 / 200000000 : ℝ)
  | ⟨18,_⟩ => (283039067 / 1000000000 : ℝ)
  | ⟨19,_⟩ => (283424441 / 1000000000 : ℝ)
  | ⟨20,_⟩ => (283808889 / 1000000000 : ℝ)
  | ⟨21,_⟩ => (284192421 / 1000000000 : ℝ)
  | ⟨22,_⟩ => (28457503 / 100000000 : ℝ)
  | ⟨23,_⟩ => (284956229 / 1000000000 : ℝ)
  | ⟨24,_⟩ => (57067403 / 200000000 : ℝ)
  | ⟨25,_⟩ => (142858221 / 500000000 : ℝ)
  | ⟨26,_⟩ => (35761933 / 125000000 : ℝ)
  | ⟨27,_⟩ => (2238071 / 7812500 : ℝ)
  | ⟨28,_⟩ => (35856227 / 125000000 : ℝ)
  | ⟨29,_⟩ => (287225649 / 1000000000 : ℝ)
  | ⟨30,_⟩ => (287600089 / 1000000000 : ℝ)
  | ⟨31,_⟩ => (57594829 / 200000000 : ℝ)
  | ⟨32,_⟩ => (144173661 / 500000000 : ℝ)
  | ⟨33,_⟩ => (72179777 / 250000000 : ℝ)
  | ⟨34,_⟩ => (14454501 / 50000000 : ℝ)
  | ⟨35,_⟩ => (144730031 / 500000000 : ℝ)
  | ⟨36,_⟩ => (289829227 / 1000000000 : ℝ)
  | ⟨37,_⟩ => (290197533 / 1000000000 : ℝ)
  | ⟨38,_⟩ => (11622599 / 40000000 : ℝ)
  | ⟨39,_⟩ => (145465523 / 500000000 : ℝ)
  | ⟨40,_⟩ => (145648129 / 500000000 : ℝ)
  | ⟨41,_⟩ => (291660619 / 1000000000 : ℝ)
  | ⟨42,_⟩ => (292024129 / 1000000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12344Cell0 :
    0 ≤ cap12344 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12344 (parameters ⟨0,by decide⟩)
      (scalarRow12344.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12344 ⟨0,by decide⟩ ∧
    (scalarRow12344.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12344 ⟨0,by decide⟩ + (scalarRow12344.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12344.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12344.targetFrame := by
  norm_num [cap12344, scalarRow12344, sourceIndex, cell12344, BstLean.Part263.envelope, parameters]

theorem repair12344Cell1 :
    0 ≤ cap12344 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12344 (parameters ⟨1,by decide⟩)
      (scalarRow12344.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12344 ⟨1,by decide⟩ ∧
    (scalarRow12344.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12344 ⟨1,by decide⟩ + (scalarRow12344.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12344.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12344.targetFrame := by
  norm_num [cap12344, scalarRow12344, sourceIndex, cell12344, BstLean.Part263.envelope, parameters]

theorem repair12344Cell2 :
    0 ≤ cap12344 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12344 (parameters ⟨2,by decide⟩)
      (scalarRow12344.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12344 ⟨2,by decide⟩ ∧
    (scalarRow12344.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12344 ⟨2,by decide⟩ + (scalarRow12344.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12344.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12344.targetFrame := by
  norm_num [cap12344, scalarRow12344, sourceIndex, cell12344, BstLean.Part263.envelope, parameters]

theorem repair12344Cell3 :
    0 ≤ cap12344 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12344 (parameters ⟨3,by decide⟩)
      (scalarRow12344.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12344 ⟨3,by decide⟩ ∧
    (scalarRow12344.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12344 ⟨3,by decide⟩ + (scalarRow12344.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12344.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12344.targetFrame := by
  norm_num [cap12344, scalarRow12344, sourceIndex, cell12344, BstLean.Part263.envelope, parameters]

theorem repair12344Cell4 :
    0 ≤ cap12344 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12344 (parameters ⟨4,by decide⟩)
      (scalarRow12344.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12344 ⟨4,by decide⟩ ∧
    (scalarRow12344.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12344 ⟨4,by decide⟩ + (scalarRow12344.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12344.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12344.targetFrame := by
  norm_num [cap12344, scalarRow12344, sourceIndex, cell12344, BstLean.Part263.envelope, parameters]

theorem repair12344Cell5 :
    0 ≤ cap12344 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12344 (parameters ⟨5,by decide⟩)
      (scalarRow12344.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12344 ⟨5,by decide⟩ ∧
    (scalarRow12344.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12344 ⟨5,by decide⟩ + (scalarRow12344.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12344.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12344.targetFrame := by
  norm_num [cap12344, scalarRow12344, sourceIndex, cell12344, BstLean.Part263.envelope, parameters]

theorem repair12344Cell6 :
    0 ≤ cap12344 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12344 (parameters ⟨6,by decide⟩)
      (scalarRow12344.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12344 ⟨6,by decide⟩ ∧
    (scalarRow12344.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12344 ⟨6,by decide⟩ + (scalarRow12344.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12344.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12344.targetFrame := by
  norm_num [cap12344, scalarRow12344, sourceIndex, cell12344, BstLean.Part263.envelope, parameters]

theorem repair12344Cell7 :
    0 ≤ cap12344 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12344 (parameters ⟨7,by decide⟩)
      (scalarRow12344.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12344 ⟨7,by decide⟩ ∧
    (scalarRow12344.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12344 ⟨7,by decide⟩ + (scalarRow12344.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12344.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12344.targetFrame := by
  norm_num [cap12344, scalarRow12344, sourceIndex, cell12344, BstLean.Part263.envelope, parameters]

theorem repair12344Cell8 :
    0 ≤ cap12344 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12344 (parameters ⟨8,by decide⟩)
      (scalarRow12344.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12344 ⟨8,by decide⟩ ∧
    (scalarRow12344.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12344 ⟨8,by decide⟩ + (scalarRow12344.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12344.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12344.targetFrame := by
  norm_num [cap12344, scalarRow12344, sourceIndex, cell12344, BstLean.Part263.envelope, parameters]

theorem repair12344Cell9 :
    0 ≤ cap12344 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12344 (parameters ⟨9,by decide⟩)
      (scalarRow12344.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12344 ⟨9,by decide⟩ ∧
    (scalarRow12344.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12344 ⟨9,by decide⟩ + (scalarRow12344.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12344.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12344.targetFrame := by
  norm_num [cap12344, scalarRow12344, sourceIndex, cell12344, BstLean.Part263.envelope, parameters]

theorem repair12344Cell10 :
    0 ≤ cap12344 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12344 (parameters ⟨10,by decide⟩)
      (scalarRow12344.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12344 ⟨10,by decide⟩ ∧
    (scalarRow12344.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12344 ⟨10,by decide⟩ + (scalarRow12344.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12344.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12344.targetFrame := by
  norm_num [cap12344, scalarRow12344, sourceIndex, cell12344, BstLean.Part263.envelope, parameters]

theorem repair12344Cell11 :
    0 ≤ cap12344 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12344 (parameters ⟨11,by decide⟩)
      (scalarRow12344.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12344 ⟨11,by decide⟩ ∧
    (scalarRow12344.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12344 ⟨11,by decide⟩ + (scalarRow12344.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12344.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12344.targetFrame := by
  norm_num [cap12344, scalarRow12344, sourceIndex, cell12344, BstLean.Part263.envelope, parameters]

theorem repair12344Cell12 :
    0 ≤ cap12344 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12344 (parameters ⟨12,by decide⟩)
      (scalarRow12344.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12344 ⟨12,by decide⟩ ∧
    (scalarRow12344.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12344 ⟨12,by decide⟩ + (scalarRow12344.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12344.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12344.targetFrame := by
  norm_num [cap12344, scalarRow12344, sourceIndex, cell12344, BstLean.Part263.envelope, parameters]

theorem repair12344Cell13 :
    0 ≤ cap12344 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12344 (parameters ⟨13,by decide⟩)
      (scalarRow12344.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12344 ⟨13,by decide⟩ ∧
    (scalarRow12344.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12344 ⟨13,by decide⟩ + (scalarRow12344.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12344.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12344.targetFrame := by
  norm_num [cap12344, scalarRow12344, sourceIndex, cell12344, BstLean.Part263.envelope, parameters]

theorem repair12344Cell14 :
    0 ≤ cap12344 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12344 (parameters ⟨14,by decide⟩)
      (scalarRow12344.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12344 ⟨14,by decide⟩ ∧
    (scalarRow12344.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12344 ⟨14,by decide⟩ + (scalarRow12344.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12344.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12344.targetFrame := by
  norm_num [cap12344, scalarRow12344, sourceIndex, cell12344, BstLean.Part263.envelope, parameters]

theorem repair12344Cell15 :
    0 ≤ cap12344 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12344 (parameters ⟨15,by decide⟩)
      (scalarRow12344.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12344 ⟨15,by decide⟩ ∧
    (scalarRow12344.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12344 ⟨15,by decide⟩ + (scalarRow12344.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12344.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12344.targetFrame := by
  norm_num [cap12344, scalarRow12344, sourceIndex, cell12344, BstLean.Part263.envelope, parameters]

theorem repair12344Cell16 :
    0 ≤ cap12344 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12344 (parameters ⟨16,by decide⟩)
      (scalarRow12344.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12344 ⟨16,by decide⟩ ∧
    (scalarRow12344.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12344 ⟨16,by decide⟩ + (scalarRow12344.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12344.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12344.targetFrame := by
  norm_num [cap12344, scalarRow12344, sourceIndex, cell12344, BstLean.Part263.envelope, parameters]

theorem repair12344Cell17 :
    0 ≤ cap12344 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12344 (parameters ⟨17,by decide⟩)
      (scalarRow12344.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12344 ⟨17,by decide⟩ ∧
    (scalarRow12344.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12344 ⟨17,by decide⟩ + (scalarRow12344.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12344.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12344.targetFrame := by
  norm_num [cap12344, scalarRow12344, sourceIndex, cell12344, BstLean.Part263.envelope, parameters]

theorem repair12344Cell18 :
    0 ≤ cap12344 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12344 (parameters ⟨18,by decide⟩)
      (scalarRow12344.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12344 ⟨18,by decide⟩ ∧
    (scalarRow12344.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12344 ⟨18,by decide⟩ + (scalarRow12344.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12344.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12344.targetFrame := by
  norm_num [cap12344, scalarRow12344, sourceIndex, cell12344, BstLean.Part263.envelope, parameters]

theorem repair12344Cell19 :
    0 ≤ cap12344 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12344 (parameters ⟨19,by decide⟩)
      (scalarRow12344.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12344 ⟨19,by decide⟩ ∧
    (scalarRow12344.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12344 ⟨19,by decide⟩ + (scalarRow12344.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12344.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12344.targetFrame := by
  norm_num [cap12344, scalarRow12344, sourceIndex, cell12344, BstLean.Part263.envelope, parameters]

theorem repair12344Cell20 :
    0 ≤ cap12344 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12344 (parameters ⟨20,by decide⟩)
      (scalarRow12344.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12344 ⟨20,by decide⟩ ∧
    (scalarRow12344.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12344 ⟨20,by decide⟩ + (scalarRow12344.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12344.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12344.targetFrame := by
  norm_num [cap12344, scalarRow12344, sourceIndex, cell12344, BstLean.Part263.envelope, parameters]

theorem repair12344Cell21 :
    0 ≤ cap12344 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12344 (parameters ⟨21,by decide⟩)
      (scalarRow12344.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12344 ⟨21,by decide⟩ ∧
    (scalarRow12344.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12344 ⟨21,by decide⟩ + (scalarRow12344.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12344.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12344.targetFrame := by
  norm_num [cap12344, scalarRow12344, sourceIndex, cell12344, BstLean.Part263.envelope, parameters]

theorem repair12344Cell22 :
    0 ≤ cap12344 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12344 (parameters ⟨22,by decide⟩)
      (scalarRow12344.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12344 ⟨22,by decide⟩ ∧
    (scalarRow12344.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12344 ⟨22,by decide⟩ + (scalarRow12344.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12344.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12344.targetFrame := by
  norm_num [cap12344, scalarRow12344, sourceIndex, cell12344, BstLean.Part263.envelope, parameters]

theorem repair12344Cell23 :
    0 ≤ cap12344 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12344 (parameters ⟨23,by decide⟩)
      (scalarRow12344.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12344 ⟨23,by decide⟩ ∧
    (scalarRow12344.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12344 ⟨23,by decide⟩ + (scalarRow12344.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12344.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12344.targetFrame := by
  norm_num [cap12344, scalarRow12344, sourceIndex, cell12344, BstLean.Part263.envelope, parameters]

theorem repair12344Cell24 :
    0 ≤ cap12344 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12344 (parameters ⟨24,by decide⟩)
      (scalarRow12344.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12344 ⟨24,by decide⟩ ∧
    (scalarRow12344.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12344 ⟨24,by decide⟩ + (scalarRow12344.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12344.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12344.targetFrame := by
  norm_num [cap12344, scalarRow12344, sourceIndex, cell12344, BstLean.Part263.envelope, parameters]

theorem repair12344Cell25 :
    0 ≤ cap12344 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12344 (parameters ⟨25,by decide⟩)
      (scalarRow12344.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12344 ⟨25,by decide⟩ ∧
    (scalarRow12344.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12344 ⟨25,by decide⟩ + (scalarRow12344.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12344.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12344.targetFrame := by
  norm_num [cap12344, scalarRow12344, sourceIndex, cell12344, BstLean.Part263.envelope, parameters]

theorem repair12344Cell26 :
    0 ≤ cap12344 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12344 (parameters ⟨26,by decide⟩)
      (scalarRow12344.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12344 ⟨26,by decide⟩ ∧
    (scalarRow12344.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12344 ⟨26,by decide⟩ + (scalarRow12344.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12344.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12344.targetFrame := by
  norm_num [cap12344, scalarRow12344, sourceIndex, cell12344, BstLean.Part263.envelope, parameters]

theorem repair12344Cell27 :
    0 ≤ cap12344 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12344 (parameters ⟨27,by decide⟩)
      (scalarRow12344.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12344 ⟨27,by decide⟩ ∧
    (scalarRow12344.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12344 ⟨27,by decide⟩ + (scalarRow12344.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12344.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12344.targetFrame := by
  norm_num [cap12344, scalarRow12344, sourceIndex, cell12344, BstLean.Part263.envelope, parameters]

theorem repair12344Cell28 :
    0 ≤ cap12344 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12344 (parameters ⟨28,by decide⟩)
      (scalarRow12344.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12344 ⟨28,by decide⟩ ∧
    (scalarRow12344.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12344 ⟨28,by decide⟩ + (scalarRow12344.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12344.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12344.targetFrame := by
  norm_num [cap12344, scalarRow12344, sourceIndex, cell12344, BstLean.Part263.envelope, parameters]

theorem repair12344Cell29 :
    0 ≤ cap12344 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12344 (parameters ⟨29,by decide⟩)
      (scalarRow12344.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12344 ⟨29,by decide⟩ ∧
    (scalarRow12344.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12344 ⟨29,by decide⟩ + (scalarRow12344.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12344.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12344.targetFrame := by
  norm_num [cap12344, scalarRow12344, sourceIndex, cell12344, BstLean.Part263.envelope, parameters]

theorem repair12344Cell30 :
    0 ≤ cap12344 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12344 (parameters ⟨30,by decide⟩)
      (scalarRow12344.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12344 ⟨30,by decide⟩ ∧
    (scalarRow12344.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12344 ⟨30,by decide⟩ + (scalarRow12344.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12344.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12344.targetFrame := by
  norm_num [cap12344, scalarRow12344, sourceIndex, cell12344, BstLean.Part263.envelope, parameters]

theorem repair12344Cell31 :
    0 ≤ cap12344 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12344 (parameters ⟨31,by decide⟩)
      (scalarRow12344.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12344 ⟨31,by decide⟩ ∧
    (scalarRow12344.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12344 ⟨31,by decide⟩ + (scalarRow12344.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12344.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12344.targetFrame := by
  norm_num [cap12344, scalarRow12344, sourceIndex, cell12344, BstLean.Part263.envelope, parameters]

theorem repair12344Cell32 :
    0 ≤ cap12344 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12344 (parameters ⟨32,by decide⟩)
      (scalarRow12344.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12344 ⟨32,by decide⟩ ∧
    (scalarRow12344.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12344 ⟨32,by decide⟩ + (scalarRow12344.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12344.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12344.targetFrame := by
  norm_num [cap12344, scalarRow12344, sourceIndex, cell12344, BstLean.Part263.envelope, parameters]

theorem repair12344Cell33 :
    0 ≤ cap12344 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12344 (parameters ⟨33,by decide⟩)
      (scalarRow12344.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12344 ⟨33,by decide⟩ ∧
    (scalarRow12344.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12344 ⟨33,by decide⟩ + (scalarRow12344.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12344.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12344.targetFrame := by
  norm_num [cap12344, scalarRow12344, sourceIndex, cell12344, BstLean.Part263.envelope, parameters]

theorem repair12344Cell34 :
    0 ≤ cap12344 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12344 (parameters ⟨34,by decide⟩)
      (scalarRow12344.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12344 ⟨34,by decide⟩ ∧
    (scalarRow12344.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12344 ⟨34,by decide⟩ + (scalarRow12344.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12344.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12344.targetFrame := by
  norm_num [cap12344, scalarRow12344, sourceIndex, cell12344, BstLean.Part263.envelope, parameters]

theorem repair12344Cell35 :
    0 ≤ cap12344 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12344 (parameters ⟨35,by decide⟩)
      (scalarRow12344.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12344 ⟨35,by decide⟩ ∧
    (scalarRow12344.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12344 ⟨35,by decide⟩ + (scalarRow12344.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12344.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12344.targetFrame := by
  norm_num [cap12344, scalarRow12344, sourceIndex, cell12344, BstLean.Part263.envelope, parameters]

theorem repair12344Cell36 :
    0 ≤ cap12344 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12344 (parameters ⟨36,by decide⟩)
      (scalarRow12344.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12344 ⟨36,by decide⟩ ∧
    (scalarRow12344.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12344 ⟨36,by decide⟩ + (scalarRow12344.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12344.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12344.targetFrame := by
  norm_num [cap12344, scalarRow12344, sourceIndex, cell12344, BstLean.Part263.envelope, parameters]

theorem repair12344Cell37 :
    0 ≤ cap12344 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12344 (parameters ⟨37,by decide⟩)
      (scalarRow12344.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12344 ⟨37,by decide⟩ ∧
    (scalarRow12344.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12344 ⟨37,by decide⟩ + (scalarRow12344.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12344.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12344.targetFrame := by
  norm_num [cap12344, scalarRow12344, sourceIndex, cell12344, BstLean.Part263.envelope, parameters]

theorem repair12344Cell38 :
    0 ≤ cap12344 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12344 (parameters ⟨38,by decide⟩)
      (scalarRow12344.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12344 ⟨38,by decide⟩ ∧
    (scalarRow12344.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12344 ⟨38,by decide⟩ + (scalarRow12344.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12344.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12344.targetFrame := by
  norm_num [cap12344, scalarRow12344, sourceIndex, cell12344, BstLean.Part263.envelope, parameters]

theorem repair12344Cell39 :
    0 ≤ cap12344 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12344 (parameters ⟨39,by decide⟩)
      (scalarRow12344.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12344 ⟨39,by decide⟩ ∧
    (scalarRow12344.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12344 ⟨39,by decide⟩ + (scalarRow12344.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12344.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12344.targetFrame := by
  norm_num [cap12344, scalarRow12344, sourceIndex, cell12344, BstLean.Part263.envelope, parameters]

theorem repair12344Cell40 :
    0 ≤ cap12344 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12344 (parameters ⟨40,by decide⟩)
      (scalarRow12344.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12344 ⟨40,by decide⟩ ∧
    (scalarRow12344.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12344 ⟨40,by decide⟩ + (scalarRow12344.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12344.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12344.targetFrame := by
  norm_num [cap12344, scalarRow12344, sourceIndex, cell12344, BstLean.Part263.envelope, parameters]

theorem repair12344Cell41 :
    0 ≤ cap12344 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12344 (parameters ⟨41,by decide⟩)
      (scalarRow12344.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12344 ⟨41,by decide⟩ ∧
    (scalarRow12344.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12344 ⟨41,by decide⟩ + (scalarRow12344.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12344.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12344.targetFrame := by
  norm_num [cap12344, scalarRow12344, sourceIndex, cell12344, BstLean.Part263.envelope, parameters]

theorem repair12344Cell42 :
    0 ≤ cap12344 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12344 (parameters ⟨42,by decide⟩)
      (scalarRow12344.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12344 ⟨42,by decide⟩ ∧
    (scalarRow12344.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12344 ⟨42,by decide⟩ + (scalarRow12344.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12344.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12344.targetFrame := by
  norm_num [cap12344, scalarRow12344, sourceIndex, cell12344, BstLean.Part263.envelope, parameters]

theorem repair12344Cells (j : Fin 43) :
    0 ≤ cap12344 j ∧
    BstLean.Part263.envelope 12344 (parameters j) (scalarRow12344.table (sourceIndex j)).upper ≤ cap12344 j ∧
    (scalarRow12344.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12344 j + (scalarRow12344.table (sourceIndex j)).centre) /
      (scalarRow12344.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12344.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12344Cell0
  | ⟨1,_⟩ => exact repair12344Cell1
  | ⟨2,_⟩ => exact repair12344Cell2
  | ⟨3,_⟩ => exact repair12344Cell3
  | ⟨4,_⟩ => exact repair12344Cell4
  | ⟨5,_⟩ => exact repair12344Cell5
  | ⟨6,_⟩ => exact repair12344Cell6
  | ⟨7,_⟩ => exact repair12344Cell7
  | ⟨8,_⟩ => exact repair12344Cell8
  | ⟨9,_⟩ => exact repair12344Cell9
  | ⟨10,_⟩ => exact repair12344Cell10
  | ⟨11,_⟩ => exact repair12344Cell11
  | ⟨12,_⟩ => exact repair12344Cell12
  | ⟨13,_⟩ => exact repair12344Cell13
  | ⟨14,_⟩ => exact repair12344Cell14
  | ⟨15,_⟩ => exact repair12344Cell15
  | ⟨16,_⟩ => exact repair12344Cell16
  | ⟨17,_⟩ => exact repair12344Cell17
  | ⟨18,_⟩ => exact repair12344Cell18
  | ⟨19,_⟩ => exact repair12344Cell19
  | ⟨20,_⟩ => exact repair12344Cell20
  | ⟨21,_⟩ => exact repair12344Cell21
  | ⟨22,_⟩ => exact repair12344Cell22
  | ⟨23,_⟩ => exact repair12344Cell23
  | ⟨24,_⟩ => exact repair12344Cell24
  | ⟨25,_⟩ => exact repair12344Cell25
  | ⟨26,_⟩ => exact repair12344Cell26
  | ⟨27,_⟩ => exact repair12344Cell27
  | ⟨28,_⟩ => exact repair12344Cell28
  | ⟨29,_⟩ => exact repair12344Cell29
  | ⟨30,_⟩ => exact repair12344Cell30
  | ⟨31,_⟩ => exact repair12344Cell31
  | ⟨32,_⟩ => exact repair12344Cell32
  | ⟨33,_⟩ => exact repair12344Cell33
  | ⟨34,_⟩ => exact repair12344Cell34
  | ⟨35,_⟩ => exact repair12344Cell35
  | ⟨36,_⟩ => exact repair12344Cell36
  | ⟨37,_⟩ => exact repair12344Cell37
  | ⟨38,_⟩ => exact repair12344Cell38
  | ⟨39,_⟩ => exact repair12344Cell39
  | ⟨40,_⟩ => exact repair12344Cell40
  | ⟨41,_⟩ => exact repair12344Cell41
  | ⟨42,_⟩ => exact repair12344Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12344 : FrameRepair 12344 scalarRow12344 where
  cap := cap12344
  cap_nonneg := fun j => (repair12344Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12344])
  endpoint := fun j => (repair12344Cells j).2.1
  endpoint_upper := fun j => (repair12344Cells j).2.2.1
  frame := fun j => (repair12344Cells j).2.2.2

noncomputable def cap12345 : Fin 43 → ℝ
  | ⟨0,_⟩ => (275943677 / 1000000000 : ℝ)
  | ⟨1,_⟩ => (69086543 / 250000000 : ℝ)
  | ⟨2,_⟩ => (276747673 / 1000000000 : ℝ)
  | ⟨3,_⟩ => (277148177 / 1000000000 : ℝ)
  | ⟨4,_⟩ => (277547691 / 1000000000 : ℝ)
  | ⟨5,_⟩ => (277946217 / 1000000000 : ℝ)
  | ⟨6,_⟩ => (139171641 / 500000000 : ℝ)
  | ⟨7,_⟩ => (139369921 / 500000000 : ℝ)
  | ⟨8,_⟩ => (279135427 / 1000000000 : ℝ)
  | ⟨9,_⟩ => (279530041 / 1000000000 : ℝ)
  | ⟨10,_⟩ => (69980921 / 250000000 : ℝ)
  | ⟨11,_⟩ => (7007897 / 25000000 : ℝ)
  | ⟨12,_⟩ => (140353799 / 500000000 : ℝ)
  | ⟨13,_⟩ => (281097871 / 1000000000 : ℝ)
  | ⟨14,_⟩ => (281488077 / 1000000000 : ℝ)
  | ⟨15,_⟩ => (4404331 / 15625000 : ℝ)
  | ⟨16,_⟩ => (282265349 / 1000000000 : ℝ)
  | ⟨17,_⟩ => (282652583 / 1000000000 : ℝ)
  | ⟨18,_⟩ => (283038879 / 1000000000 : ℝ)
  | ⟨19,_⟩ => (283424247 / 1000000000 : ℝ)
  | ⟨20,_⟩ => (17738043 / 62500000 : ℝ)
  | ⟨21,_⟩ => (142096107 / 500000000 : ℝ)
  | ⟨22,_⟩ => (284574817 / 1000000000 : ℝ)
  | ⟨23,_⟩ => (284956009 / 1000000000 : ℝ)
  | ⟨24,_⟩ => (28533679 / 100000000 : ℝ)
  | ⟨25,_⟩ => (28571621 / 100000000 : ℝ)
  | ⟨26,_⟩ => (143047613 / 500000000 : ℝ)
  | ⟨27,_⟩ => (71618211 / 250000000 : ℝ)
  | ⟨28,_⟩ => (143424783 / 500000000 : ℝ)
  | ⟨29,_⟩ => (287225393 / 1000000000 : ℝ)
  | ⟨30,_⟩ => (287599827 / 1000000000 : ℝ)
  | ⟨31,_⟩ => (287973877 / 1000000000 : ℝ)
  | ⟨32,_⟩ => (288347047 / 1000000000 : ℝ)
  | ⟨33,_⟩ => (72179707 / 250000000 : ℝ)
  | ⟨34,_⟩ => (144544867 / 500000000 : ℝ)
  | ⟨35,_⟩ => (28945977 / 100000000 : ℝ)
  | ⟨36,_⟩ => (289828929 / 1000000000 : ℝ)
  | ⟨37,_⟩ => (290197229 / 1000000000 : ℝ)
  | ⟨38,_⟩ => (58112933 / 200000000 : ℝ)
  | ⟨39,_⟩ => (29093073 / 100000000 : ℝ)
  | ⟨40,_⟩ => (4551499 / 15625000 : ℝ)
  | ⟨41,_⟩ => (291660291 / 1000000000 : ℝ)
  | ⟨42,_⟩ => (58404759 / 200000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12345Cell0 :
    0 ≤ cap12345 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12345 (parameters ⟨0,by decide⟩)
      (scalarRow12345.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12345 ⟨0,by decide⟩ ∧
    (scalarRow12345.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12345 ⟨0,by decide⟩ + (scalarRow12345.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12345.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12345.targetFrame := by
  norm_num [cap12345, scalarRow12345, sourceIndex, cell12345, BstLean.Part263.envelope, parameters]

theorem repair12345Cell1 :
    0 ≤ cap12345 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12345 (parameters ⟨1,by decide⟩)
      (scalarRow12345.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12345 ⟨1,by decide⟩ ∧
    (scalarRow12345.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12345 ⟨1,by decide⟩ + (scalarRow12345.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12345.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12345.targetFrame := by
  norm_num [cap12345, scalarRow12345, sourceIndex, cell12345, BstLean.Part263.envelope, parameters]

theorem repair12345Cell2 :
    0 ≤ cap12345 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12345 (parameters ⟨2,by decide⟩)
      (scalarRow12345.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12345 ⟨2,by decide⟩ ∧
    (scalarRow12345.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12345 ⟨2,by decide⟩ + (scalarRow12345.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12345.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12345.targetFrame := by
  norm_num [cap12345, scalarRow12345, sourceIndex, cell12345, BstLean.Part263.envelope, parameters]

theorem repair12345Cell3 :
    0 ≤ cap12345 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12345 (parameters ⟨3,by decide⟩)
      (scalarRow12345.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12345 ⟨3,by decide⟩ ∧
    (scalarRow12345.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12345 ⟨3,by decide⟩ + (scalarRow12345.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12345.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12345.targetFrame := by
  norm_num [cap12345, scalarRow12345, sourceIndex, cell12345, BstLean.Part263.envelope, parameters]

theorem repair12345Cell4 :
    0 ≤ cap12345 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12345 (parameters ⟨4,by decide⟩)
      (scalarRow12345.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12345 ⟨4,by decide⟩ ∧
    (scalarRow12345.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12345 ⟨4,by decide⟩ + (scalarRow12345.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12345.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12345.targetFrame := by
  norm_num [cap12345, scalarRow12345, sourceIndex, cell12345, BstLean.Part263.envelope, parameters]

theorem repair12345Cell5 :
    0 ≤ cap12345 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12345 (parameters ⟨5,by decide⟩)
      (scalarRow12345.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12345 ⟨5,by decide⟩ ∧
    (scalarRow12345.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12345 ⟨5,by decide⟩ + (scalarRow12345.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12345.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12345.targetFrame := by
  norm_num [cap12345, scalarRow12345, sourceIndex, cell12345, BstLean.Part263.envelope, parameters]

theorem repair12345Cell6 :
    0 ≤ cap12345 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12345 (parameters ⟨6,by decide⟩)
      (scalarRow12345.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12345 ⟨6,by decide⟩ ∧
    (scalarRow12345.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12345 ⟨6,by decide⟩ + (scalarRow12345.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12345.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12345.targetFrame := by
  norm_num [cap12345, scalarRow12345, sourceIndex, cell12345, BstLean.Part263.envelope, parameters]

theorem repair12345Cell7 :
    0 ≤ cap12345 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12345 (parameters ⟨7,by decide⟩)
      (scalarRow12345.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12345 ⟨7,by decide⟩ ∧
    (scalarRow12345.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12345 ⟨7,by decide⟩ + (scalarRow12345.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12345.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12345.targetFrame := by
  norm_num [cap12345, scalarRow12345, sourceIndex, cell12345, BstLean.Part263.envelope, parameters]

theorem repair12345Cell8 :
    0 ≤ cap12345 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12345 (parameters ⟨8,by decide⟩)
      (scalarRow12345.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12345 ⟨8,by decide⟩ ∧
    (scalarRow12345.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12345 ⟨8,by decide⟩ + (scalarRow12345.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12345.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12345.targetFrame := by
  norm_num [cap12345, scalarRow12345, sourceIndex, cell12345, BstLean.Part263.envelope, parameters]

theorem repair12345Cell9 :
    0 ≤ cap12345 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12345 (parameters ⟨9,by decide⟩)
      (scalarRow12345.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12345 ⟨9,by decide⟩ ∧
    (scalarRow12345.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12345 ⟨9,by decide⟩ + (scalarRow12345.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12345.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12345.targetFrame := by
  norm_num [cap12345, scalarRow12345, sourceIndex, cell12345, BstLean.Part263.envelope, parameters]

theorem repair12345Cell10 :
    0 ≤ cap12345 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12345 (parameters ⟨10,by decide⟩)
      (scalarRow12345.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12345 ⟨10,by decide⟩ ∧
    (scalarRow12345.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12345 ⟨10,by decide⟩ + (scalarRow12345.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12345.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12345.targetFrame := by
  norm_num [cap12345, scalarRow12345, sourceIndex, cell12345, BstLean.Part263.envelope, parameters]

theorem repair12345Cell11 :
    0 ≤ cap12345 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12345 (parameters ⟨11,by decide⟩)
      (scalarRow12345.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12345 ⟨11,by decide⟩ ∧
    (scalarRow12345.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12345 ⟨11,by decide⟩ + (scalarRow12345.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12345.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12345.targetFrame := by
  norm_num [cap12345, scalarRow12345, sourceIndex, cell12345, BstLean.Part263.envelope, parameters]

theorem repair12345Cell12 :
    0 ≤ cap12345 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12345 (parameters ⟨12,by decide⟩)
      (scalarRow12345.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12345 ⟨12,by decide⟩ ∧
    (scalarRow12345.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12345 ⟨12,by decide⟩ + (scalarRow12345.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12345.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12345.targetFrame := by
  norm_num [cap12345, scalarRow12345, sourceIndex, cell12345, BstLean.Part263.envelope, parameters]

theorem repair12345Cell13 :
    0 ≤ cap12345 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12345 (parameters ⟨13,by decide⟩)
      (scalarRow12345.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12345 ⟨13,by decide⟩ ∧
    (scalarRow12345.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12345 ⟨13,by decide⟩ + (scalarRow12345.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12345.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12345.targetFrame := by
  norm_num [cap12345, scalarRow12345, sourceIndex, cell12345, BstLean.Part263.envelope, parameters]

theorem repair12345Cell14 :
    0 ≤ cap12345 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12345 (parameters ⟨14,by decide⟩)
      (scalarRow12345.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12345 ⟨14,by decide⟩ ∧
    (scalarRow12345.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12345 ⟨14,by decide⟩ + (scalarRow12345.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12345.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12345.targetFrame := by
  norm_num [cap12345, scalarRow12345, sourceIndex, cell12345, BstLean.Part263.envelope, parameters]

theorem repair12345Cell15 :
    0 ≤ cap12345 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12345 (parameters ⟨15,by decide⟩)
      (scalarRow12345.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12345 ⟨15,by decide⟩ ∧
    (scalarRow12345.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12345 ⟨15,by decide⟩ + (scalarRow12345.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12345.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12345.targetFrame := by
  norm_num [cap12345, scalarRow12345, sourceIndex, cell12345, BstLean.Part263.envelope, parameters]

theorem repair12345Cell16 :
    0 ≤ cap12345 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12345 (parameters ⟨16,by decide⟩)
      (scalarRow12345.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12345 ⟨16,by decide⟩ ∧
    (scalarRow12345.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12345 ⟨16,by decide⟩ + (scalarRow12345.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12345.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12345.targetFrame := by
  norm_num [cap12345, scalarRow12345, sourceIndex, cell12345, BstLean.Part263.envelope, parameters]

theorem repair12345Cell17 :
    0 ≤ cap12345 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12345 (parameters ⟨17,by decide⟩)
      (scalarRow12345.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12345 ⟨17,by decide⟩ ∧
    (scalarRow12345.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12345 ⟨17,by decide⟩ + (scalarRow12345.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12345.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12345.targetFrame := by
  norm_num [cap12345, scalarRow12345, sourceIndex, cell12345, BstLean.Part263.envelope, parameters]

theorem repair12345Cell18 :
    0 ≤ cap12345 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12345 (parameters ⟨18,by decide⟩)
      (scalarRow12345.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12345 ⟨18,by decide⟩ ∧
    (scalarRow12345.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12345 ⟨18,by decide⟩ + (scalarRow12345.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12345.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12345.targetFrame := by
  norm_num [cap12345, scalarRow12345, sourceIndex, cell12345, BstLean.Part263.envelope, parameters]

theorem repair12345Cell19 :
    0 ≤ cap12345 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12345 (parameters ⟨19,by decide⟩)
      (scalarRow12345.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12345 ⟨19,by decide⟩ ∧
    (scalarRow12345.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12345 ⟨19,by decide⟩ + (scalarRow12345.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12345.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12345.targetFrame := by
  norm_num [cap12345, scalarRow12345, sourceIndex, cell12345, BstLean.Part263.envelope, parameters]

theorem repair12345Cell20 :
    0 ≤ cap12345 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12345 (parameters ⟨20,by decide⟩)
      (scalarRow12345.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12345 ⟨20,by decide⟩ ∧
    (scalarRow12345.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12345 ⟨20,by decide⟩ + (scalarRow12345.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12345.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12345.targetFrame := by
  norm_num [cap12345, scalarRow12345, sourceIndex, cell12345, BstLean.Part263.envelope, parameters]

theorem repair12345Cell21 :
    0 ≤ cap12345 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12345 (parameters ⟨21,by decide⟩)
      (scalarRow12345.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12345 ⟨21,by decide⟩ ∧
    (scalarRow12345.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12345 ⟨21,by decide⟩ + (scalarRow12345.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12345.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12345.targetFrame := by
  norm_num [cap12345, scalarRow12345, sourceIndex, cell12345, BstLean.Part263.envelope, parameters]

theorem repair12345Cell22 :
    0 ≤ cap12345 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12345 (parameters ⟨22,by decide⟩)
      (scalarRow12345.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12345 ⟨22,by decide⟩ ∧
    (scalarRow12345.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12345 ⟨22,by decide⟩ + (scalarRow12345.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12345.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12345.targetFrame := by
  norm_num [cap12345, scalarRow12345, sourceIndex, cell12345, BstLean.Part263.envelope, parameters]

theorem repair12345Cell23 :
    0 ≤ cap12345 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12345 (parameters ⟨23,by decide⟩)
      (scalarRow12345.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12345 ⟨23,by decide⟩ ∧
    (scalarRow12345.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12345 ⟨23,by decide⟩ + (scalarRow12345.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12345.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12345.targetFrame := by
  norm_num [cap12345, scalarRow12345, sourceIndex, cell12345, BstLean.Part263.envelope, parameters]

theorem repair12345Cell24 :
    0 ≤ cap12345 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12345 (parameters ⟨24,by decide⟩)
      (scalarRow12345.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12345 ⟨24,by decide⟩ ∧
    (scalarRow12345.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12345 ⟨24,by decide⟩ + (scalarRow12345.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12345.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12345.targetFrame := by
  norm_num [cap12345, scalarRow12345, sourceIndex, cell12345, BstLean.Part263.envelope, parameters]

theorem repair12345Cell25 :
    0 ≤ cap12345 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12345 (parameters ⟨25,by decide⟩)
      (scalarRow12345.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12345 ⟨25,by decide⟩ ∧
    (scalarRow12345.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12345 ⟨25,by decide⟩ + (scalarRow12345.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12345.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12345.targetFrame := by
  norm_num [cap12345, scalarRow12345, sourceIndex, cell12345, BstLean.Part263.envelope, parameters]

theorem repair12345Cell26 :
    0 ≤ cap12345 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12345 (parameters ⟨26,by decide⟩)
      (scalarRow12345.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12345 ⟨26,by decide⟩ ∧
    (scalarRow12345.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12345 ⟨26,by decide⟩ + (scalarRow12345.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12345.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12345.targetFrame := by
  norm_num [cap12345, scalarRow12345, sourceIndex, cell12345, BstLean.Part263.envelope, parameters]

theorem repair12345Cell27 :
    0 ≤ cap12345 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12345 (parameters ⟨27,by decide⟩)
      (scalarRow12345.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12345 ⟨27,by decide⟩ ∧
    (scalarRow12345.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12345 ⟨27,by decide⟩ + (scalarRow12345.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12345.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12345.targetFrame := by
  norm_num [cap12345, scalarRow12345, sourceIndex, cell12345, BstLean.Part263.envelope, parameters]

theorem repair12345Cell28 :
    0 ≤ cap12345 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12345 (parameters ⟨28,by decide⟩)
      (scalarRow12345.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12345 ⟨28,by decide⟩ ∧
    (scalarRow12345.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12345 ⟨28,by decide⟩ + (scalarRow12345.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12345.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12345.targetFrame := by
  norm_num [cap12345, scalarRow12345, sourceIndex, cell12345, BstLean.Part263.envelope, parameters]

theorem repair12345Cell29 :
    0 ≤ cap12345 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12345 (parameters ⟨29,by decide⟩)
      (scalarRow12345.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12345 ⟨29,by decide⟩ ∧
    (scalarRow12345.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12345 ⟨29,by decide⟩ + (scalarRow12345.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12345.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12345.targetFrame := by
  norm_num [cap12345, scalarRow12345, sourceIndex, cell12345, BstLean.Part263.envelope, parameters]

theorem repair12345Cell30 :
    0 ≤ cap12345 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12345 (parameters ⟨30,by decide⟩)
      (scalarRow12345.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12345 ⟨30,by decide⟩ ∧
    (scalarRow12345.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12345 ⟨30,by decide⟩ + (scalarRow12345.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12345.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12345.targetFrame := by
  norm_num [cap12345, scalarRow12345, sourceIndex, cell12345, BstLean.Part263.envelope, parameters]

theorem repair12345Cell31 :
    0 ≤ cap12345 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12345 (parameters ⟨31,by decide⟩)
      (scalarRow12345.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12345 ⟨31,by decide⟩ ∧
    (scalarRow12345.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12345 ⟨31,by decide⟩ + (scalarRow12345.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12345.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12345.targetFrame := by
  norm_num [cap12345, scalarRow12345, sourceIndex, cell12345, BstLean.Part263.envelope, parameters]

theorem repair12345Cell32 :
    0 ≤ cap12345 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12345 (parameters ⟨32,by decide⟩)
      (scalarRow12345.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12345 ⟨32,by decide⟩ ∧
    (scalarRow12345.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12345 ⟨32,by decide⟩ + (scalarRow12345.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12345.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12345.targetFrame := by
  norm_num [cap12345, scalarRow12345, sourceIndex, cell12345, BstLean.Part263.envelope, parameters]

theorem repair12345Cell33 :
    0 ≤ cap12345 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12345 (parameters ⟨33,by decide⟩)
      (scalarRow12345.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12345 ⟨33,by decide⟩ ∧
    (scalarRow12345.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12345 ⟨33,by decide⟩ + (scalarRow12345.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12345.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12345.targetFrame := by
  norm_num [cap12345, scalarRow12345, sourceIndex, cell12345, BstLean.Part263.envelope, parameters]

theorem repair12345Cell34 :
    0 ≤ cap12345 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12345 (parameters ⟨34,by decide⟩)
      (scalarRow12345.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12345 ⟨34,by decide⟩ ∧
    (scalarRow12345.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12345 ⟨34,by decide⟩ + (scalarRow12345.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12345.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12345.targetFrame := by
  norm_num [cap12345, scalarRow12345, sourceIndex, cell12345, BstLean.Part263.envelope, parameters]

theorem repair12345Cell35 :
    0 ≤ cap12345 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12345 (parameters ⟨35,by decide⟩)
      (scalarRow12345.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12345 ⟨35,by decide⟩ ∧
    (scalarRow12345.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12345 ⟨35,by decide⟩ + (scalarRow12345.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12345.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12345.targetFrame := by
  norm_num [cap12345, scalarRow12345, sourceIndex, cell12345, BstLean.Part263.envelope, parameters]

theorem repair12345Cell36 :
    0 ≤ cap12345 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12345 (parameters ⟨36,by decide⟩)
      (scalarRow12345.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12345 ⟨36,by decide⟩ ∧
    (scalarRow12345.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12345 ⟨36,by decide⟩ + (scalarRow12345.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12345.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12345.targetFrame := by
  norm_num [cap12345, scalarRow12345, sourceIndex, cell12345, BstLean.Part263.envelope, parameters]

theorem repair12345Cell37 :
    0 ≤ cap12345 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12345 (parameters ⟨37,by decide⟩)
      (scalarRow12345.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12345 ⟨37,by decide⟩ ∧
    (scalarRow12345.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12345 ⟨37,by decide⟩ + (scalarRow12345.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12345.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12345.targetFrame := by
  norm_num [cap12345, scalarRow12345, sourceIndex, cell12345, BstLean.Part263.envelope, parameters]

theorem repair12345Cell38 :
    0 ≤ cap12345 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12345 (parameters ⟨38,by decide⟩)
      (scalarRow12345.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12345 ⟨38,by decide⟩ ∧
    (scalarRow12345.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12345 ⟨38,by decide⟩ + (scalarRow12345.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12345.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12345.targetFrame := by
  norm_num [cap12345, scalarRow12345, sourceIndex, cell12345, BstLean.Part263.envelope, parameters]

theorem repair12345Cell39 :
    0 ≤ cap12345 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12345 (parameters ⟨39,by decide⟩)
      (scalarRow12345.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12345 ⟨39,by decide⟩ ∧
    (scalarRow12345.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12345 ⟨39,by decide⟩ + (scalarRow12345.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12345.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12345.targetFrame := by
  norm_num [cap12345, scalarRow12345, sourceIndex, cell12345, BstLean.Part263.envelope, parameters]

theorem repair12345Cell40 :
    0 ≤ cap12345 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12345 (parameters ⟨40,by decide⟩)
      (scalarRow12345.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12345 ⟨40,by decide⟩ ∧
    (scalarRow12345.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12345 ⟨40,by decide⟩ + (scalarRow12345.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12345.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12345.targetFrame := by
  norm_num [cap12345, scalarRow12345, sourceIndex, cell12345, BstLean.Part263.envelope, parameters]

theorem repair12345Cell41 :
    0 ≤ cap12345 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12345 (parameters ⟨41,by decide⟩)
      (scalarRow12345.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12345 ⟨41,by decide⟩ ∧
    (scalarRow12345.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12345 ⟨41,by decide⟩ + (scalarRow12345.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12345.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12345.targetFrame := by
  norm_num [cap12345, scalarRow12345, sourceIndex, cell12345, BstLean.Part263.envelope, parameters]

theorem repair12345Cell42 :
    0 ≤ cap12345 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12345 (parameters ⟨42,by decide⟩)
      (scalarRow12345.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12345 ⟨42,by decide⟩ ∧
    (scalarRow12345.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12345 ⟨42,by decide⟩ + (scalarRow12345.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12345.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12345.targetFrame := by
  norm_num [cap12345, scalarRow12345, sourceIndex, cell12345, BstLean.Part263.envelope, parameters]

theorem repair12345Cells (j : Fin 43) :
    0 ≤ cap12345 j ∧
    BstLean.Part263.envelope 12345 (parameters j) (scalarRow12345.table (sourceIndex j)).upper ≤ cap12345 j ∧
    (scalarRow12345.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12345 j + (scalarRow12345.table (sourceIndex j)).centre) /
      (scalarRow12345.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12345.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12345Cell0
  | ⟨1,_⟩ => exact repair12345Cell1
  | ⟨2,_⟩ => exact repair12345Cell2
  | ⟨3,_⟩ => exact repair12345Cell3
  | ⟨4,_⟩ => exact repair12345Cell4
  | ⟨5,_⟩ => exact repair12345Cell5
  | ⟨6,_⟩ => exact repair12345Cell6
  | ⟨7,_⟩ => exact repair12345Cell7
  | ⟨8,_⟩ => exact repair12345Cell8
  | ⟨9,_⟩ => exact repair12345Cell9
  | ⟨10,_⟩ => exact repair12345Cell10
  | ⟨11,_⟩ => exact repair12345Cell11
  | ⟨12,_⟩ => exact repair12345Cell12
  | ⟨13,_⟩ => exact repair12345Cell13
  | ⟨14,_⟩ => exact repair12345Cell14
  | ⟨15,_⟩ => exact repair12345Cell15
  | ⟨16,_⟩ => exact repair12345Cell16
  | ⟨17,_⟩ => exact repair12345Cell17
  | ⟨18,_⟩ => exact repair12345Cell18
  | ⟨19,_⟩ => exact repair12345Cell19
  | ⟨20,_⟩ => exact repair12345Cell20
  | ⟨21,_⟩ => exact repair12345Cell21
  | ⟨22,_⟩ => exact repair12345Cell22
  | ⟨23,_⟩ => exact repair12345Cell23
  | ⟨24,_⟩ => exact repair12345Cell24
  | ⟨25,_⟩ => exact repair12345Cell25
  | ⟨26,_⟩ => exact repair12345Cell26
  | ⟨27,_⟩ => exact repair12345Cell27
  | ⟨28,_⟩ => exact repair12345Cell28
  | ⟨29,_⟩ => exact repair12345Cell29
  | ⟨30,_⟩ => exact repair12345Cell30
  | ⟨31,_⟩ => exact repair12345Cell31
  | ⟨32,_⟩ => exact repair12345Cell32
  | ⟨33,_⟩ => exact repair12345Cell33
  | ⟨34,_⟩ => exact repair12345Cell34
  | ⟨35,_⟩ => exact repair12345Cell35
  | ⟨36,_⟩ => exact repair12345Cell36
  | ⟨37,_⟩ => exact repair12345Cell37
  | ⟨38,_⟩ => exact repair12345Cell38
  | ⟨39,_⟩ => exact repair12345Cell39
  | ⟨40,_⟩ => exact repair12345Cell40
  | ⟨41,_⟩ => exact repair12345Cell41
  | ⟨42,_⟩ => exact repair12345Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12345 : FrameRepair 12345 scalarRow12345 where
  cap := cap12345
  cap_nonneg := fun j => (repair12345Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12345])
  endpoint := fun j => (repair12345Cells j).2.1
  endpoint_upper := fun j => (repair12345Cells j).2.2.1
  frame := fun j => (repair12345Cells j).2.2.2

noncomputable def cap12346 : Fin 43 → ℝ
  | ⟨0,_⟩ => (137971801 / 500000000 : ℝ)
  | ⟨1,_⟩ => (27634609 / 100000000 : ℝ)
  | ⟨2,_⟩ => (55349517 / 200000000 : ℝ)
  | ⟨3,_⟩ => (277148083 / 1000000000 : ℝ)
  | ⟨4,_⟩ => (277547591 / 1000000000 : ℝ)
  | ⟨5,_⟩ => (27794611 / 100000000 : ℝ)
  | ⟨6,_⟩ => (278343169 / 1000000000 : ℝ)
  | ⟨7,_⟩ => (278739723 / 1000000000 : ℝ)
  | ⟨8,_⟩ => (279135301 / 1000000000 : ℝ)
  | ⟨9,_⟩ => (69882477 / 250000000 : ℝ)
  | ⟨10,_⟩ => (55984709 / 200000000 : ℝ)
  | ⟨11,_⟩ => (56063147 / 200000000 : ℝ)
  | ⟨12,_⟩ => (280707447 / 1000000000 : ℝ)
  | ⟨13,_⟩ => (281097713 / 1000000000 : ℝ)
  | ⟨14,_⟩ => (281487913 / 1000000000 : ℝ)
  | ⟨15,_⟩ => (140938507 / 500000000 : ℝ)
  | ⟨16,_⟩ => (70566293 / 250000000 : ℝ)
  | ⟨17,_⟩ => (706631 / 2500000 : ℝ)
  | ⟨18,_⟩ => (28303869 / 100000000 : ℝ)
  | ⟨19,_⟩ => (70856013 / 250000000 : ℝ)
  | ⟨20,_⟩ => (283808487 / 1000000000 : ℝ)
  | ⟨21,_⟩ => (284192007 / 1000000000 : ℝ)
  | ⟨22,_⟩ => (284574603 / 1000000000 : ℝ)
  | ⟨23,_⟩ => (28495579 / 100000000 : ℝ)
  | ⟨24,_⟩ => (71334141 / 250000000 : ℝ)
  | ⟨25,_⟩ => (142857989 / 500000000 : ℝ)
  | ⟨26,_⟩ => (286094989 / 1000000000 : ℝ)
  | ⟨27,_⟩ => (1432363 / 5000000 : ℝ)
  | ⟨28,_⟩ => (71712329 / 250000000 : ℝ)
  | ⟨29,_⟩ => (287225137 / 1000000000 : ℝ)
  | ⟨30,_⟩ => (57519913 / 200000000 : ℝ)
  | ⟨31,_⟩ => (287973609 / 1000000000 : ℝ)
  | ⟨32,_⟩ => (288346773 / 1000000000 : ℝ)
  | ⟨33,_⟩ => (72179637 / 250000000 : ℝ)
  | ⟨34,_⟩ => (36136181 / 125000000 : ℝ)
  | ⟨35,_⟩ => (144729739 / 500000000 : ℝ)
  | ⟨36,_⟩ => (289828631 / 1000000000 : ℝ)
  | ⟨37,_⟩ => (11607877 / 40000000 : ℝ)
  | ⟨38,_⟩ => (72641089 / 250000000 : ℝ)
  | ⟨39,_⟩ => (145465207 / 500000000 : ℝ)
  | ⟨40,_⟩ => (145647807 / 500000000 : ℝ)
  | ⟨41,_⟩ => (72914991 / 250000000 : ℝ)
  | ⟨42,_⟩ => (146011731 / 500000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12346Cell0 :
    0 ≤ cap12346 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12346 (parameters ⟨0,by decide⟩)
      (scalarRow12346.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12346 ⟨0,by decide⟩ ∧
    (scalarRow12346.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12346 ⟨0,by decide⟩ + (scalarRow12346.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12346.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12346.targetFrame := by
  norm_num [cap12346, scalarRow12346, sourceIndex, cell12346, BstLean.Part263.envelope, parameters]

theorem repair12346Cell1 :
    0 ≤ cap12346 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12346 (parameters ⟨1,by decide⟩)
      (scalarRow12346.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12346 ⟨1,by decide⟩ ∧
    (scalarRow12346.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12346 ⟨1,by decide⟩ + (scalarRow12346.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12346.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12346.targetFrame := by
  norm_num [cap12346, scalarRow12346, sourceIndex, cell12346, BstLean.Part263.envelope, parameters]

theorem repair12346Cell2 :
    0 ≤ cap12346 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12346 (parameters ⟨2,by decide⟩)
      (scalarRow12346.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12346 ⟨2,by decide⟩ ∧
    (scalarRow12346.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12346 ⟨2,by decide⟩ + (scalarRow12346.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12346.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12346.targetFrame := by
  norm_num [cap12346, scalarRow12346, sourceIndex, cell12346, BstLean.Part263.envelope, parameters]

theorem repair12346Cell3 :
    0 ≤ cap12346 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12346 (parameters ⟨3,by decide⟩)
      (scalarRow12346.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12346 ⟨3,by decide⟩ ∧
    (scalarRow12346.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12346 ⟨3,by decide⟩ + (scalarRow12346.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12346.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12346.targetFrame := by
  norm_num [cap12346, scalarRow12346, sourceIndex, cell12346, BstLean.Part263.envelope, parameters]

theorem repair12346Cell4 :
    0 ≤ cap12346 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12346 (parameters ⟨4,by decide⟩)
      (scalarRow12346.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12346 ⟨4,by decide⟩ ∧
    (scalarRow12346.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12346 ⟨4,by decide⟩ + (scalarRow12346.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12346.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12346.targetFrame := by
  norm_num [cap12346, scalarRow12346, sourceIndex, cell12346, BstLean.Part263.envelope, parameters]

theorem repair12346Cell5 :
    0 ≤ cap12346 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12346 (parameters ⟨5,by decide⟩)
      (scalarRow12346.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12346 ⟨5,by decide⟩ ∧
    (scalarRow12346.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12346 ⟨5,by decide⟩ + (scalarRow12346.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12346.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12346.targetFrame := by
  norm_num [cap12346, scalarRow12346, sourceIndex, cell12346, BstLean.Part263.envelope, parameters]

theorem repair12346Cell6 :
    0 ≤ cap12346 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12346 (parameters ⟨6,by decide⟩)
      (scalarRow12346.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12346 ⟨6,by decide⟩ ∧
    (scalarRow12346.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12346 ⟨6,by decide⟩ + (scalarRow12346.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12346.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12346.targetFrame := by
  norm_num [cap12346, scalarRow12346, sourceIndex, cell12346, BstLean.Part263.envelope, parameters]

theorem repair12346Cell7 :
    0 ≤ cap12346 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12346 (parameters ⟨7,by decide⟩)
      (scalarRow12346.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12346 ⟨7,by decide⟩ ∧
    (scalarRow12346.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12346 ⟨7,by decide⟩ + (scalarRow12346.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12346.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12346.targetFrame := by
  norm_num [cap12346, scalarRow12346, sourceIndex, cell12346, BstLean.Part263.envelope, parameters]

theorem repair12346Cell8 :
    0 ≤ cap12346 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12346 (parameters ⟨8,by decide⟩)
      (scalarRow12346.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12346 ⟨8,by decide⟩ ∧
    (scalarRow12346.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12346 ⟨8,by decide⟩ + (scalarRow12346.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12346.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12346.targetFrame := by
  norm_num [cap12346, scalarRow12346, sourceIndex, cell12346, BstLean.Part263.envelope, parameters]

theorem repair12346Cell9 :
    0 ≤ cap12346 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12346 (parameters ⟨9,by decide⟩)
      (scalarRow12346.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12346 ⟨9,by decide⟩ ∧
    (scalarRow12346.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12346 ⟨9,by decide⟩ + (scalarRow12346.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12346.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12346.targetFrame := by
  norm_num [cap12346, scalarRow12346, sourceIndex, cell12346, BstLean.Part263.envelope, parameters]

theorem repair12346Cell10 :
    0 ≤ cap12346 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12346 (parameters ⟨10,by decide⟩)
      (scalarRow12346.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12346 ⟨10,by decide⟩ ∧
    (scalarRow12346.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12346 ⟨10,by decide⟩ + (scalarRow12346.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12346.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12346.targetFrame := by
  norm_num [cap12346, scalarRow12346, sourceIndex, cell12346, BstLean.Part263.envelope, parameters]

theorem repair12346Cell11 :
    0 ≤ cap12346 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12346 (parameters ⟨11,by decide⟩)
      (scalarRow12346.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12346 ⟨11,by decide⟩ ∧
    (scalarRow12346.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12346 ⟨11,by decide⟩ + (scalarRow12346.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12346.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12346.targetFrame := by
  norm_num [cap12346, scalarRow12346, sourceIndex, cell12346, BstLean.Part263.envelope, parameters]

theorem repair12346Cell12 :
    0 ≤ cap12346 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12346 (parameters ⟨12,by decide⟩)
      (scalarRow12346.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12346 ⟨12,by decide⟩ ∧
    (scalarRow12346.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12346 ⟨12,by decide⟩ + (scalarRow12346.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12346.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12346.targetFrame := by
  norm_num [cap12346, scalarRow12346, sourceIndex, cell12346, BstLean.Part263.envelope, parameters]

theorem repair12346Cell13 :
    0 ≤ cap12346 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12346 (parameters ⟨13,by decide⟩)
      (scalarRow12346.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12346 ⟨13,by decide⟩ ∧
    (scalarRow12346.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12346 ⟨13,by decide⟩ + (scalarRow12346.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12346.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12346.targetFrame := by
  norm_num [cap12346, scalarRow12346, sourceIndex, cell12346, BstLean.Part263.envelope, parameters]

theorem repair12346Cell14 :
    0 ≤ cap12346 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12346 (parameters ⟨14,by decide⟩)
      (scalarRow12346.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12346 ⟨14,by decide⟩ ∧
    (scalarRow12346.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12346 ⟨14,by decide⟩ + (scalarRow12346.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12346.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12346.targetFrame := by
  norm_num [cap12346, scalarRow12346, sourceIndex, cell12346, BstLean.Part263.envelope, parameters]

theorem repair12346Cell15 :
    0 ≤ cap12346 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12346 (parameters ⟨15,by decide⟩)
      (scalarRow12346.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12346 ⟨15,by decide⟩ ∧
    (scalarRow12346.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12346 ⟨15,by decide⟩ + (scalarRow12346.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12346.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12346.targetFrame := by
  norm_num [cap12346, scalarRow12346, sourceIndex, cell12346, BstLean.Part263.envelope, parameters]

theorem repair12346Cell16 :
    0 ≤ cap12346 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12346 (parameters ⟨16,by decide⟩)
      (scalarRow12346.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12346 ⟨16,by decide⟩ ∧
    (scalarRow12346.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12346 ⟨16,by decide⟩ + (scalarRow12346.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12346.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12346.targetFrame := by
  norm_num [cap12346, scalarRow12346, sourceIndex, cell12346, BstLean.Part263.envelope, parameters]

theorem repair12346Cell17 :
    0 ≤ cap12346 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12346 (parameters ⟨17,by decide⟩)
      (scalarRow12346.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12346 ⟨17,by decide⟩ ∧
    (scalarRow12346.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12346 ⟨17,by decide⟩ + (scalarRow12346.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12346.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12346.targetFrame := by
  norm_num [cap12346, scalarRow12346, sourceIndex, cell12346, BstLean.Part263.envelope, parameters]

theorem repair12346Cell18 :
    0 ≤ cap12346 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12346 (parameters ⟨18,by decide⟩)
      (scalarRow12346.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12346 ⟨18,by decide⟩ ∧
    (scalarRow12346.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12346 ⟨18,by decide⟩ + (scalarRow12346.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12346.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12346.targetFrame := by
  norm_num [cap12346, scalarRow12346, sourceIndex, cell12346, BstLean.Part263.envelope, parameters]

theorem repair12346Cell19 :
    0 ≤ cap12346 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12346 (parameters ⟨19,by decide⟩)
      (scalarRow12346.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12346 ⟨19,by decide⟩ ∧
    (scalarRow12346.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12346 ⟨19,by decide⟩ + (scalarRow12346.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12346.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12346.targetFrame := by
  norm_num [cap12346, scalarRow12346, sourceIndex, cell12346, BstLean.Part263.envelope, parameters]

theorem repair12346Cell20 :
    0 ≤ cap12346 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12346 (parameters ⟨20,by decide⟩)
      (scalarRow12346.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12346 ⟨20,by decide⟩ ∧
    (scalarRow12346.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12346 ⟨20,by decide⟩ + (scalarRow12346.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12346.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12346.targetFrame := by
  norm_num [cap12346, scalarRow12346, sourceIndex, cell12346, BstLean.Part263.envelope, parameters]

theorem repair12346Cell21 :
    0 ≤ cap12346 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12346 (parameters ⟨21,by decide⟩)
      (scalarRow12346.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12346 ⟨21,by decide⟩ ∧
    (scalarRow12346.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12346 ⟨21,by decide⟩ + (scalarRow12346.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12346.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12346.targetFrame := by
  norm_num [cap12346, scalarRow12346, sourceIndex, cell12346, BstLean.Part263.envelope, parameters]

theorem repair12346Cell22 :
    0 ≤ cap12346 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12346 (parameters ⟨22,by decide⟩)
      (scalarRow12346.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12346 ⟨22,by decide⟩ ∧
    (scalarRow12346.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12346 ⟨22,by decide⟩ + (scalarRow12346.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12346.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12346.targetFrame := by
  norm_num [cap12346, scalarRow12346, sourceIndex, cell12346, BstLean.Part263.envelope, parameters]

theorem repair12346Cell23 :
    0 ≤ cap12346 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12346 (parameters ⟨23,by decide⟩)
      (scalarRow12346.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12346 ⟨23,by decide⟩ ∧
    (scalarRow12346.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12346 ⟨23,by decide⟩ + (scalarRow12346.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12346.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12346.targetFrame := by
  norm_num [cap12346, scalarRow12346, sourceIndex, cell12346, BstLean.Part263.envelope, parameters]

theorem repair12346Cell24 :
    0 ≤ cap12346 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12346 (parameters ⟨24,by decide⟩)
      (scalarRow12346.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12346 ⟨24,by decide⟩ ∧
    (scalarRow12346.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12346 ⟨24,by decide⟩ + (scalarRow12346.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12346.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12346.targetFrame := by
  norm_num [cap12346, scalarRow12346, sourceIndex, cell12346, BstLean.Part263.envelope, parameters]

theorem repair12346Cell25 :
    0 ≤ cap12346 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12346 (parameters ⟨25,by decide⟩)
      (scalarRow12346.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12346 ⟨25,by decide⟩ ∧
    (scalarRow12346.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12346 ⟨25,by decide⟩ + (scalarRow12346.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12346.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12346.targetFrame := by
  norm_num [cap12346, scalarRow12346, sourceIndex, cell12346, BstLean.Part263.envelope, parameters]

theorem repair12346Cell26 :
    0 ≤ cap12346 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12346 (parameters ⟨26,by decide⟩)
      (scalarRow12346.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12346 ⟨26,by decide⟩ ∧
    (scalarRow12346.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12346 ⟨26,by decide⟩ + (scalarRow12346.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12346.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12346.targetFrame := by
  norm_num [cap12346, scalarRow12346, sourceIndex, cell12346, BstLean.Part263.envelope, parameters]

theorem repair12346Cell27 :
    0 ≤ cap12346 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12346 (parameters ⟨27,by decide⟩)
      (scalarRow12346.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12346 ⟨27,by decide⟩ ∧
    (scalarRow12346.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12346 ⟨27,by decide⟩ + (scalarRow12346.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12346.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12346.targetFrame := by
  norm_num [cap12346, scalarRow12346, sourceIndex, cell12346, BstLean.Part263.envelope, parameters]

theorem repair12346Cell28 :
    0 ≤ cap12346 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12346 (parameters ⟨28,by decide⟩)
      (scalarRow12346.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12346 ⟨28,by decide⟩ ∧
    (scalarRow12346.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12346 ⟨28,by decide⟩ + (scalarRow12346.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12346.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12346.targetFrame := by
  norm_num [cap12346, scalarRow12346, sourceIndex, cell12346, BstLean.Part263.envelope, parameters]

theorem repair12346Cell29 :
    0 ≤ cap12346 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12346 (parameters ⟨29,by decide⟩)
      (scalarRow12346.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12346 ⟨29,by decide⟩ ∧
    (scalarRow12346.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12346 ⟨29,by decide⟩ + (scalarRow12346.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12346.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12346.targetFrame := by
  norm_num [cap12346, scalarRow12346, sourceIndex, cell12346, BstLean.Part263.envelope, parameters]

theorem repair12346Cell30 :
    0 ≤ cap12346 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12346 (parameters ⟨30,by decide⟩)
      (scalarRow12346.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12346 ⟨30,by decide⟩ ∧
    (scalarRow12346.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12346 ⟨30,by decide⟩ + (scalarRow12346.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12346.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12346.targetFrame := by
  norm_num [cap12346, scalarRow12346, sourceIndex, cell12346, BstLean.Part263.envelope, parameters]

theorem repair12346Cell31 :
    0 ≤ cap12346 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12346 (parameters ⟨31,by decide⟩)
      (scalarRow12346.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12346 ⟨31,by decide⟩ ∧
    (scalarRow12346.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12346 ⟨31,by decide⟩ + (scalarRow12346.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12346.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12346.targetFrame := by
  norm_num [cap12346, scalarRow12346, sourceIndex, cell12346, BstLean.Part263.envelope, parameters]

theorem repair12346Cell32 :
    0 ≤ cap12346 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12346 (parameters ⟨32,by decide⟩)
      (scalarRow12346.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12346 ⟨32,by decide⟩ ∧
    (scalarRow12346.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12346 ⟨32,by decide⟩ + (scalarRow12346.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12346.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12346.targetFrame := by
  norm_num [cap12346, scalarRow12346, sourceIndex, cell12346, BstLean.Part263.envelope, parameters]

theorem repair12346Cell33 :
    0 ≤ cap12346 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12346 (parameters ⟨33,by decide⟩)
      (scalarRow12346.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12346 ⟨33,by decide⟩ ∧
    (scalarRow12346.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12346 ⟨33,by decide⟩ + (scalarRow12346.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12346.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12346.targetFrame := by
  norm_num [cap12346, scalarRow12346, sourceIndex, cell12346, BstLean.Part263.envelope, parameters]

theorem repair12346Cell34 :
    0 ≤ cap12346 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12346 (parameters ⟨34,by decide⟩)
      (scalarRow12346.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12346 ⟨34,by decide⟩ ∧
    (scalarRow12346.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12346 ⟨34,by decide⟩ + (scalarRow12346.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12346.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12346.targetFrame := by
  norm_num [cap12346, scalarRow12346, sourceIndex, cell12346, BstLean.Part263.envelope, parameters]

theorem repair12346Cell35 :
    0 ≤ cap12346 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12346 (parameters ⟨35,by decide⟩)
      (scalarRow12346.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12346 ⟨35,by decide⟩ ∧
    (scalarRow12346.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12346 ⟨35,by decide⟩ + (scalarRow12346.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12346.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12346.targetFrame := by
  norm_num [cap12346, scalarRow12346, sourceIndex, cell12346, BstLean.Part263.envelope, parameters]

theorem repair12346Cell36 :
    0 ≤ cap12346 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12346 (parameters ⟨36,by decide⟩)
      (scalarRow12346.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12346 ⟨36,by decide⟩ ∧
    (scalarRow12346.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12346 ⟨36,by decide⟩ + (scalarRow12346.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12346.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12346.targetFrame := by
  norm_num [cap12346, scalarRow12346, sourceIndex, cell12346, BstLean.Part263.envelope, parameters]

theorem repair12346Cell37 :
    0 ≤ cap12346 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12346 (parameters ⟨37,by decide⟩)
      (scalarRow12346.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12346 ⟨37,by decide⟩ ∧
    (scalarRow12346.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12346 ⟨37,by decide⟩ + (scalarRow12346.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12346.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12346.targetFrame := by
  norm_num [cap12346, scalarRow12346, sourceIndex, cell12346, BstLean.Part263.envelope, parameters]

theorem repair12346Cell38 :
    0 ≤ cap12346 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12346 (parameters ⟨38,by decide⟩)
      (scalarRow12346.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12346 ⟨38,by decide⟩ ∧
    (scalarRow12346.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12346 ⟨38,by decide⟩ + (scalarRow12346.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12346.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12346.targetFrame := by
  norm_num [cap12346, scalarRow12346, sourceIndex, cell12346, BstLean.Part263.envelope, parameters]

theorem repair12346Cell39 :
    0 ≤ cap12346 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12346 (parameters ⟨39,by decide⟩)
      (scalarRow12346.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12346 ⟨39,by decide⟩ ∧
    (scalarRow12346.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12346 ⟨39,by decide⟩ + (scalarRow12346.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12346.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12346.targetFrame := by
  norm_num [cap12346, scalarRow12346, sourceIndex, cell12346, BstLean.Part263.envelope, parameters]

theorem repair12346Cell40 :
    0 ≤ cap12346 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12346 (parameters ⟨40,by decide⟩)
      (scalarRow12346.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12346 ⟨40,by decide⟩ ∧
    (scalarRow12346.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12346 ⟨40,by decide⟩ + (scalarRow12346.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12346.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12346.targetFrame := by
  norm_num [cap12346, scalarRow12346, sourceIndex, cell12346, BstLean.Part263.envelope, parameters]

theorem repair12346Cell41 :
    0 ≤ cap12346 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12346 (parameters ⟨41,by decide⟩)
      (scalarRow12346.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12346 ⟨41,by decide⟩ ∧
    (scalarRow12346.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12346 ⟨41,by decide⟩ + (scalarRow12346.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12346.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12346.targetFrame := by
  norm_num [cap12346, scalarRow12346, sourceIndex, cell12346, BstLean.Part263.envelope, parameters]

theorem repair12346Cell42 :
    0 ≤ cap12346 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12346 (parameters ⟨42,by decide⟩)
      (scalarRow12346.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12346 ⟨42,by decide⟩ ∧
    (scalarRow12346.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12346 ⟨42,by decide⟩ + (scalarRow12346.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12346.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12346.targetFrame := by
  norm_num [cap12346, scalarRow12346, sourceIndex, cell12346, BstLean.Part263.envelope, parameters]

theorem repair12346Cells (j : Fin 43) :
    0 ≤ cap12346 j ∧
    BstLean.Part263.envelope 12346 (parameters j) (scalarRow12346.table (sourceIndex j)).upper ≤ cap12346 j ∧
    (scalarRow12346.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12346 j + (scalarRow12346.table (sourceIndex j)).centre) /
      (scalarRow12346.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12346.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12346Cell0
  | ⟨1,_⟩ => exact repair12346Cell1
  | ⟨2,_⟩ => exact repair12346Cell2
  | ⟨3,_⟩ => exact repair12346Cell3
  | ⟨4,_⟩ => exact repair12346Cell4
  | ⟨5,_⟩ => exact repair12346Cell5
  | ⟨6,_⟩ => exact repair12346Cell6
  | ⟨7,_⟩ => exact repair12346Cell7
  | ⟨8,_⟩ => exact repair12346Cell8
  | ⟨9,_⟩ => exact repair12346Cell9
  | ⟨10,_⟩ => exact repair12346Cell10
  | ⟨11,_⟩ => exact repair12346Cell11
  | ⟨12,_⟩ => exact repair12346Cell12
  | ⟨13,_⟩ => exact repair12346Cell13
  | ⟨14,_⟩ => exact repair12346Cell14
  | ⟨15,_⟩ => exact repair12346Cell15
  | ⟨16,_⟩ => exact repair12346Cell16
  | ⟨17,_⟩ => exact repair12346Cell17
  | ⟨18,_⟩ => exact repair12346Cell18
  | ⟨19,_⟩ => exact repair12346Cell19
  | ⟨20,_⟩ => exact repair12346Cell20
  | ⟨21,_⟩ => exact repair12346Cell21
  | ⟨22,_⟩ => exact repair12346Cell22
  | ⟨23,_⟩ => exact repair12346Cell23
  | ⟨24,_⟩ => exact repair12346Cell24
  | ⟨25,_⟩ => exact repair12346Cell25
  | ⟨26,_⟩ => exact repair12346Cell26
  | ⟨27,_⟩ => exact repair12346Cell27
  | ⟨28,_⟩ => exact repair12346Cell28
  | ⟨29,_⟩ => exact repair12346Cell29
  | ⟨30,_⟩ => exact repair12346Cell30
  | ⟨31,_⟩ => exact repair12346Cell31
  | ⟨32,_⟩ => exact repair12346Cell32
  | ⟨33,_⟩ => exact repair12346Cell33
  | ⟨34,_⟩ => exact repair12346Cell34
  | ⟨35,_⟩ => exact repair12346Cell35
  | ⟨36,_⟩ => exact repair12346Cell36
  | ⟨37,_⟩ => exact repair12346Cell37
  | ⟨38,_⟩ => exact repair12346Cell38
  | ⟨39,_⟩ => exact repair12346Cell39
  | ⟨40,_⟩ => exact repair12346Cell40
  | ⟨41,_⟩ => exact repair12346Cell41
  | ⟨42,_⟩ => exact repair12346Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12346 : FrameRepair 12346 scalarRow12346 where
  cap := cap12346
  cap_nonneg := fun j => (repair12346Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12346])
  endpoint := fun j => (repair12346Cells j).2.1
  endpoint_upper := fun j => (repair12346Cells j).2.2.1
  frame := fun j => (repair12346Cells j).2.2.2

noncomputable def cap12347 : Fin 43 → ℝ
  | ⟨0,_⟩ => (275943527 / 1000000000 : ℝ)
  | ⟨1,_⟩ => (276346009 / 1000000000 : ℝ)
  | ⟨2,_⟩ => (276747497 / 1000000000 : ℝ)
  | ⟨3,_⟩ => (277147989 / 1000000000 : ℝ)
  | ⟨4,_⟩ => (27754749 / 100000000 : ℝ)
  | ⟨5,_⟩ => (277946003 / 1000000000 : ℝ)
  | ⟨6,_⟩ => (17396441 / 62500000 : ℝ)
  | ⟨7,_⟩ => (278739603 / 1000000000 : ℝ)
  | ⟨8,_⟩ => (11165407 / 40000000 : ℝ)
  | ⟨9,_⟩ => (17470611 / 62500000 : ℝ)
  | ⟨10,_⟩ => (279923407 / 1000000000 : ℝ)
  | ⟨11,_⟩ => (28031559 / 100000000 : ℝ)
  | ⟨12,_⟩ => (8772103 / 31250000 : ℝ)
  | ⟨13,_⟩ => (70274389 / 250000000 : ℝ)
  | ⟨14,_⟩ => (281487749 / 1000000000 : ℝ)
  | ⟨15,_⟩ => (70469211 / 250000000 : ℝ)
  | ⟨16,_⟩ => (70566249 / 250000000 : ℝ)
  | ⟨17,_⟩ => (141326109 / 500000000 : ℝ)
  | ⟨18,_⟩ => (283038501 / 1000000000 : ℝ)
  | ⟨19,_⟩ => (283423857 / 1000000000 : ℝ)
  | ⟨20,_⟩ => (141904143 / 500000000 : ℝ)
  | ⟨21,_⟩ => (1420959 / 5000000 : ℝ)
  | ⟨22,_⟩ => (28457439 / 100000000 : ℝ)
  | ⟨23,_⟩ => (28495557 / 100000000 : ℝ)
  | ⟨24,_⟩ => (285336339 / 1000000000 : ℝ)
  | ⟨25,_⟩ => (285715747 / 1000000000 : ℝ)
  | ⟨26,_⟩ => (286094751 / 1000000000 : ℝ)
  | ⟨27,_⟩ => (71618089 / 250000000 : ℝ)
  | ⟨28,_⟩ => (143424533 / 500000000 : ℝ)
  | ⟨29,_⟩ => (287224881 / 1000000000 : ℝ)
  | ⟨30,_⟩ => (287599303 / 1000000000 : ℝ)
  | ⟨31,_⟩ => (287973341 / 1000000000 : ℝ)
  | ⟨32,_⟩ => (288346499 / 1000000000 : ℝ)
  | ⟨33,_⟩ => (72179567 / 250000000 : ℝ)
  | ⟨34,_⟩ => (144544581 / 500000000 : ℝ)
  | ⟨35,_⟩ => (144729593 / 500000000 : ℝ)
  | ⟨36,_⟩ => (289828333 / 1000000000 : ℝ)
  | ⟨37,_⟩ => (290196621 / 1000000000 : ℝ)
  | ⟨38,_⟩ => (145282023 / 500000000 : ℝ)
  | ⟨39,_⟩ => (145465049 / 500000000 : ℝ)
  | ⟨40,_⟩ => (72823823 / 250000000 : ℝ)
  | ⟨41,_⟩ => (72914909 / 250000000 : ℝ)
  | ⟨42,_⟩ => (36502891 / 125000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12347Cell0 :
    0 ≤ cap12347 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12347 (parameters ⟨0,by decide⟩)
      (scalarRow12347.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12347 ⟨0,by decide⟩ ∧
    (scalarRow12347.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12347 ⟨0,by decide⟩ + (scalarRow12347.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12347.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12347.targetFrame := by
  norm_num [cap12347, scalarRow12347, sourceIndex, cell12347, BstLean.Part263.envelope, parameters]

theorem repair12347Cell1 :
    0 ≤ cap12347 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12347 (parameters ⟨1,by decide⟩)
      (scalarRow12347.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12347 ⟨1,by decide⟩ ∧
    (scalarRow12347.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12347 ⟨1,by decide⟩ + (scalarRow12347.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12347.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12347.targetFrame := by
  norm_num [cap12347, scalarRow12347, sourceIndex, cell12347, BstLean.Part263.envelope, parameters]

theorem repair12347Cell2 :
    0 ≤ cap12347 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12347 (parameters ⟨2,by decide⟩)
      (scalarRow12347.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12347 ⟨2,by decide⟩ ∧
    (scalarRow12347.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12347 ⟨2,by decide⟩ + (scalarRow12347.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12347.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12347.targetFrame := by
  norm_num [cap12347, scalarRow12347, sourceIndex, cell12347, BstLean.Part263.envelope, parameters]

theorem repair12347Cell3 :
    0 ≤ cap12347 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12347 (parameters ⟨3,by decide⟩)
      (scalarRow12347.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12347 ⟨3,by decide⟩ ∧
    (scalarRow12347.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12347 ⟨3,by decide⟩ + (scalarRow12347.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12347.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12347.targetFrame := by
  norm_num [cap12347, scalarRow12347, sourceIndex, cell12347, BstLean.Part263.envelope, parameters]

theorem repair12347Cell4 :
    0 ≤ cap12347 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12347 (parameters ⟨4,by decide⟩)
      (scalarRow12347.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12347 ⟨4,by decide⟩ ∧
    (scalarRow12347.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12347 ⟨4,by decide⟩ + (scalarRow12347.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12347.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12347.targetFrame := by
  norm_num [cap12347, scalarRow12347, sourceIndex, cell12347, BstLean.Part263.envelope, parameters]

theorem repair12347Cell5 :
    0 ≤ cap12347 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12347 (parameters ⟨5,by decide⟩)
      (scalarRow12347.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12347 ⟨5,by decide⟩ ∧
    (scalarRow12347.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12347 ⟨5,by decide⟩ + (scalarRow12347.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12347.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12347.targetFrame := by
  norm_num [cap12347, scalarRow12347, sourceIndex, cell12347, BstLean.Part263.envelope, parameters]

theorem repair12347Cell6 :
    0 ≤ cap12347 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12347 (parameters ⟨6,by decide⟩)
      (scalarRow12347.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12347 ⟨6,by decide⟩ ∧
    (scalarRow12347.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12347 ⟨6,by decide⟩ + (scalarRow12347.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12347.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12347.targetFrame := by
  norm_num [cap12347, scalarRow12347, sourceIndex, cell12347, BstLean.Part263.envelope, parameters]

theorem repair12347Cell7 :
    0 ≤ cap12347 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12347 (parameters ⟨7,by decide⟩)
      (scalarRow12347.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12347 ⟨7,by decide⟩ ∧
    (scalarRow12347.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12347 ⟨7,by decide⟩ + (scalarRow12347.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12347.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12347.targetFrame := by
  norm_num [cap12347, scalarRow12347, sourceIndex, cell12347, BstLean.Part263.envelope, parameters]

theorem repair12347Cell8 :
    0 ≤ cap12347 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12347 (parameters ⟨8,by decide⟩)
      (scalarRow12347.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12347 ⟨8,by decide⟩ ∧
    (scalarRow12347.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12347 ⟨8,by decide⟩ + (scalarRow12347.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12347.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12347.targetFrame := by
  norm_num [cap12347, scalarRow12347, sourceIndex, cell12347, BstLean.Part263.envelope, parameters]

theorem repair12347Cell9 :
    0 ≤ cap12347 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12347 (parameters ⟨9,by decide⟩)
      (scalarRow12347.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12347 ⟨9,by decide⟩ ∧
    (scalarRow12347.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12347 ⟨9,by decide⟩ + (scalarRow12347.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12347.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12347.targetFrame := by
  norm_num [cap12347, scalarRow12347, sourceIndex, cell12347, BstLean.Part263.envelope, parameters]

theorem repair12347Cell10 :
    0 ≤ cap12347 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12347 (parameters ⟨10,by decide⟩)
      (scalarRow12347.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12347 ⟨10,by decide⟩ ∧
    (scalarRow12347.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12347 ⟨10,by decide⟩ + (scalarRow12347.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12347.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12347.targetFrame := by
  norm_num [cap12347, scalarRow12347, sourceIndex, cell12347, BstLean.Part263.envelope, parameters]

theorem repair12347Cell11 :
    0 ≤ cap12347 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12347 (parameters ⟨11,by decide⟩)
      (scalarRow12347.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12347 ⟨11,by decide⟩ ∧
    (scalarRow12347.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12347 ⟨11,by decide⟩ + (scalarRow12347.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12347.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12347.targetFrame := by
  norm_num [cap12347, scalarRow12347, sourceIndex, cell12347, BstLean.Part263.envelope, parameters]

theorem repair12347Cell12 :
    0 ≤ cap12347 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12347 (parameters ⟨12,by decide⟩)
      (scalarRow12347.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12347 ⟨12,by decide⟩ ∧
    (scalarRow12347.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12347 ⟨12,by decide⟩ + (scalarRow12347.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12347.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12347.targetFrame := by
  norm_num [cap12347, scalarRow12347, sourceIndex, cell12347, BstLean.Part263.envelope, parameters]

theorem repair12347Cell13 :
    0 ≤ cap12347 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12347 (parameters ⟨13,by decide⟩)
      (scalarRow12347.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12347 ⟨13,by decide⟩ ∧
    (scalarRow12347.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12347 ⟨13,by decide⟩ + (scalarRow12347.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12347.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12347.targetFrame := by
  norm_num [cap12347, scalarRow12347, sourceIndex, cell12347, BstLean.Part263.envelope, parameters]

theorem repair12347Cell14 :
    0 ≤ cap12347 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12347 (parameters ⟨14,by decide⟩)
      (scalarRow12347.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12347 ⟨14,by decide⟩ ∧
    (scalarRow12347.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12347 ⟨14,by decide⟩ + (scalarRow12347.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12347.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12347.targetFrame := by
  norm_num [cap12347, scalarRow12347, sourceIndex, cell12347, BstLean.Part263.envelope, parameters]

theorem repair12347Cell15 :
    0 ≤ cap12347 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12347 (parameters ⟨15,by decide⟩)
      (scalarRow12347.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12347 ⟨15,by decide⟩ ∧
    (scalarRow12347.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12347 ⟨15,by decide⟩ + (scalarRow12347.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12347.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12347.targetFrame := by
  norm_num [cap12347, scalarRow12347, sourceIndex, cell12347, BstLean.Part263.envelope, parameters]

theorem repair12347Cell16 :
    0 ≤ cap12347 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12347 (parameters ⟨16,by decide⟩)
      (scalarRow12347.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12347 ⟨16,by decide⟩ ∧
    (scalarRow12347.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12347 ⟨16,by decide⟩ + (scalarRow12347.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12347.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12347.targetFrame := by
  norm_num [cap12347, scalarRow12347, sourceIndex, cell12347, BstLean.Part263.envelope, parameters]

theorem repair12347Cell17 :
    0 ≤ cap12347 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12347 (parameters ⟨17,by decide⟩)
      (scalarRow12347.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12347 ⟨17,by decide⟩ ∧
    (scalarRow12347.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12347 ⟨17,by decide⟩ + (scalarRow12347.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12347.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12347.targetFrame := by
  norm_num [cap12347, scalarRow12347, sourceIndex, cell12347, BstLean.Part263.envelope, parameters]

theorem repair12347Cell18 :
    0 ≤ cap12347 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12347 (parameters ⟨18,by decide⟩)
      (scalarRow12347.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12347 ⟨18,by decide⟩ ∧
    (scalarRow12347.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12347 ⟨18,by decide⟩ + (scalarRow12347.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12347.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12347.targetFrame := by
  norm_num [cap12347, scalarRow12347, sourceIndex, cell12347, BstLean.Part263.envelope, parameters]

theorem repair12347Cell19 :
    0 ≤ cap12347 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12347 (parameters ⟨19,by decide⟩)
      (scalarRow12347.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12347 ⟨19,by decide⟩ ∧
    (scalarRow12347.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12347 ⟨19,by decide⟩ + (scalarRow12347.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12347.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12347.targetFrame := by
  norm_num [cap12347, scalarRow12347, sourceIndex, cell12347, BstLean.Part263.envelope, parameters]

theorem repair12347Cell20 :
    0 ≤ cap12347 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12347 (parameters ⟨20,by decide⟩)
      (scalarRow12347.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12347 ⟨20,by decide⟩ ∧
    (scalarRow12347.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12347 ⟨20,by decide⟩ + (scalarRow12347.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12347.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12347.targetFrame := by
  norm_num [cap12347, scalarRow12347, sourceIndex, cell12347, BstLean.Part263.envelope, parameters]

theorem repair12347Cell21 :
    0 ≤ cap12347 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12347 (parameters ⟨21,by decide⟩)
      (scalarRow12347.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12347 ⟨21,by decide⟩ ∧
    (scalarRow12347.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12347 ⟨21,by decide⟩ + (scalarRow12347.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12347.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12347.targetFrame := by
  norm_num [cap12347, scalarRow12347, sourceIndex, cell12347, BstLean.Part263.envelope, parameters]

theorem repair12347Cell22 :
    0 ≤ cap12347 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12347 (parameters ⟨22,by decide⟩)
      (scalarRow12347.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12347 ⟨22,by decide⟩ ∧
    (scalarRow12347.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12347 ⟨22,by decide⟩ + (scalarRow12347.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12347.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12347.targetFrame := by
  norm_num [cap12347, scalarRow12347, sourceIndex, cell12347, BstLean.Part263.envelope, parameters]

theorem repair12347Cell23 :
    0 ≤ cap12347 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12347 (parameters ⟨23,by decide⟩)
      (scalarRow12347.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12347 ⟨23,by decide⟩ ∧
    (scalarRow12347.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12347 ⟨23,by decide⟩ + (scalarRow12347.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12347.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12347.targetFrame := by
  norm_num [cap12347, scalarRow12347, sourceIndex, cell12347, BstLean.Part263.envelope, parameters]

theorem repair12347Cell24 :
    0 ≤ cap12347 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12347 (parameters ⟨24,by decide⟩)
      (scalarRow12347.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12347 ⟨24,by decide⟩ ∧
    (scalarRow12347.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12347 ⟨24,by decide⟩ + (scalarRow12347.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12347.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12347.targetFrame := by
  norm_num [cap12347, scalarRow12347, sourceIndex, cell12347, BstLean.Part263.envelope, parameters]

theorem repair12347Cell25 :
    0 ≤ cap12347 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12347 (parameters ⟨25,by decide⟩)
      (scalarRow12347.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12347 ⟨25,by decide⟩ ∧
    (scalarRow12347.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12347 ⟨25,by decide⟩ + (scalarRow12347.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12347.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12347.targetFrame := by
  norm_num [cap12347, scalarRow12347, sourceIndex, cell12347, BstLean.Part263.envelope, parameters]

theorem repair12347Cell26 :
    0 ≤ cap12347 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12347 (parameters ⟨26,by decide⟩)
      (scalarRow12347.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12347 ⟨26,by decide⟩ ∧
    (scalarRow12347.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12347 ⟨26,by decide⟩ + (scalarRow12347.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12347.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12347.targetFrame := by
  norm_num [cap12347, scalarRow12347, sourceIndex, cell12347, BstLean.Part263.envelope, parameters]

theorem repair12347Cell27 :
    0 ≤ cap12347 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12347 (parameters ⟨27,by decide⟩)
      (scalarRow12347.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12347 ⟨27,by decide⟩ ∧
    (scalarRow12347.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12347 ⟨27,by decide⟩ + (scalarRow12347.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12347.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12347.targetFrame := by
  norm_num [cap12347, scalarRow12347, sourceIndex, cell12347, BstLean.Part263.envelope, parameters]

theorem repair12347Cell28 :
    0 ≤ cap12347 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12347 (parameters ⟨28,by decide⟩)
      (scalarRow12347.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12347 ⟨28,by decide⟩ ∧
    (scalarRow12347.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12347 ⟨28,by decide⟩ + (scalarRow12347.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12347.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12347.targetFrame := by
  norm_num [cap12347, scalarRow12347, sourceIndex, cell12347, BstLean.Part263.envelope, parameters]

theorem repair12347Cell29 :
    0 ≤ cap12347 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12347 (parameters ⟨29,by decide⟩)
      (scalarRow12347.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12347 ⟨29,by decide⟩ ∧
    (scalarRow12347.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12347 ⟨29,by decide⟩ + (scalarRow12347.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12347.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12347.targetFrame := by
  norm_num [cap12347, scalarRow12347, sourceIndex, cell12347, BstLean.Part263.envelope, parameters]

theorem repair12347Cell30 :
    0 ≤ cap12347 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12347 (parameters ⟨30,by decide⟩)
      (scalarRow12347.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12347 ⟨30,by decide⟩ ∧
    (scalarRow12347.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12347 ⟨30,by decide⟩ + (scalarRow12347.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12347.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12347.targetFrame := by
  norm_num [cap12347, scalarRow12347, sourceIndex, cell12347, BstLean.Part263.envelope, parameters]

theorem repair12347Cell31 :
    0 ≤ cap12347 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12347 (parameters ⟨31,by decide⟩)
      (scalarRow12347.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12347 ⟨31,by decide⟩ ∧
    (scalarRow12347.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12347 ⟨31,by decide⟩ + (scalarRow12347.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12347.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12347.targetFrame := by
  norm_num [cap12347, scalarRow12347, sourceIndex, cell12347, BstLean.Part263.envelope, parameters]

theorem repair12347Cell32 :
    0 ≤ cap12347 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12347 (parameters ⟨32,by decide⟩)
      (scalarRow12347.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12347 ⟨32,by decide⟩ ∧
    (scalarRow12347.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12347 ⟨32,by decide⟩ + (scalarRow12347.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12347.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12347.targetFrame := by
  norm_num [cap12347, scalarRow12347, sourceIndex, cell12347, BstLean.Part263.envelope, parameters]

theorem repair12347Cell33 :
    0 ≤ cap12347 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12347 (parameters ⟨33,by decide⟩)
      (scalarRow12347.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12347 ⟨33,by decide⟩ ∧
    (scalarRow12347.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12347 ⟨33,by decide⟩ + (scalarRow12347.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12347.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12347.targetFrame := by
  norm_num [cap12347, scalarRow12347, sourceIndex, cell12347, BstLean.Part263.envelope, parameters]

theorem repair12347Cell34 :
    0 ≤ cap12347 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12347 (parameters ⟨34,by decide⟩)
      (scalarRow12347.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12347 ⟨34,by decide⟩ ∧
    (scalarRow12347.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12347 ⟨34,by decide⟩ + (scalarRow12347.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12347.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12347.targetFrame := by
  norm_num [cap12347, scalarRow12347, sourceIndex, cell12347, BstLean.Part263.envelope, parameters]

theorem repair12347Cell35 :
    0 ≤ cap12347 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12347 (parameters ⟨35,by decide⟩)
      (scalarRow12347.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12347 ⟨35,by decide⟩ ∧
    (scalarRow12347.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12347 ⟨35,by decide⟩ + (scalarRow12347.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12347.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12347.targetFrame := by
  norm_num [cap12347, scalarRow12347, sourceIndex, cell12347, BstLean.Part263.envelope, parameters]

theorem repair12347Cell36 :
    0 ≤ cap12347 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12347 (parameters ⟨36,by decide⟩)
      (scalarRow12347.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12347 ⟨36,by decide⟩ ∧
    (scalarRow12347.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12347 ⟨36,by decide⟩ + (scalarRow12347.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12347.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12347.targetFrame := by
  norm_num [cap12347, scalarRow12347, sourceIndex, cell12347, BstLean.Part263.envelope, parameters]

theorem repair12347Cell37 :
    0 ≤ cap12347 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12347 (parameters ⟨37,by decide⟩)
      (scalarRow12347.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12347 ⟨37,by decide⟩ ∧
    (scalarRow12347.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12347 ⟨37,by decide⟩ + (scalarRow12347.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12347.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12347.targetFrame := by
  norm_num [cap12347, scalarRow12347, sourceIndex, cell12347, BstLean.Part263.envelope, parameters]

theorem repair12347Cell38 :
    0 ≤ cap12347 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12347 (parameters ⟨38,by decide⟩)
      (scalarRow12347.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12347 ⟨38,by decide⟩ ∧
    (scalarRow12347.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12347 ⟨38,by decide⟩ + (scalarRow12347.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12347.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12347.targetFrame := by
  norm_num [cap12347, scalarRow12347, sourceIndex, cell12347, BstLean.Part263.envelope, parameters]

theorem repair12347Cell39 :
    0 ≤ cap12347 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12347 (parameters ⟨39,by decide⟩)
      (scalarRow12347.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12347 ⟨39,by decide⟩ ∧
    (scalarRow12347.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12347 ⟨39,by decide⟩ + (scalarRow12347.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12347.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12347.targetFrame := by
  norm_num [cap12347, scalarRow12347, sourceIndex, cell12347, BstLean.Part263.envelope, parameters]

theorem repair12347Cell40 :
    0 ≤ cap12347 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12347 (parameters ⟨40,by decide⟩)
      (scalarRow12347.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12347 ⟨40,by decide⟩ ∧
    (scalarRow12347.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12347 ⟨40,by decide⟩ + (scalarRow12347.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12347.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12347.targetFrame := by
  norm_num [cap12347, scalarRow12347, sourceIndex, cell12347, BstLean.Part263.envelope, parameters]

theorem repair12347Cell41 :
    0 ≤ cap12347 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12347 (parameters ⟨41,by decide⟩)
      (scalarRow12347.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12347 ⟨41,by decide⟩ ∧
    (scalarRow12347.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12347 ⟨41,by decide⟩ + (scalarRow12347.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12347.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12347.targetFrame := by
  norm_num [cap12347, scalarRow12347, sourceIndex, cell12347, BstLean.Part263.envelope, parameters]

theorem repair12347Cell42 :
    0 ≤ cap12347 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12347 (parameters ⟨42,by decide⟩)
      (scalarRow12347.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12347 ⟨42,by decide⟩ ∧
    (scalarRow12347.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12347 ⟨42,by decide⟩ + (scalarRow12347.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12347.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12347.targetFrame := by
  norm_num [cap12347, scalarRow12347, sourceIndex, cell12347, BstLean.Part263.envelope, parameters]

theorem repair12347Cells (j : Fin 43) :
    0 ≤ cap12347 j ∧
    BstLean.Part263.envelope 12347 (parameters j) (scalarRow12347.table (sourceIndex j)).upper ≤ cap12347 j ∧
    (scalarRow12347.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12347 j + (scalarRow12347.table (sourceIndex j)).centre) /
      (scalarRow12347.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12347.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12347Cell0
  | ⟨1,_⟩ => exact repair12347Cell1
  | ⟨2,_⟩ => exact repair12347Cell2
  | ⟨3,_⟩ => exact repair12347Cell3
  | ⟨4,_⟩ => exact repair12347Cell4
  | ⟨5,_⟩ => exact repair12347Cell5
  | ⟨6,_⟩ => exact repair12347Cell6
  | ⟨7,_⟩ => exact repair12347Cell7
  | ⟨8,_⟩ => exact repair12347Cell8
  | ⟨9,_⟩ => exact repair12347Cell9
  | ⟨10,_⟩ => exact repair12347Cell10
  | ⟨11,_⟩ => exact repair12347Cell11
  | ⟨12,_⟩ => exact repair12347Cell12
  | ⟨13,_⟩ => exact repair12347Cell13
  | ⟨14,_⟩ => exact repair12347Cell14
  | ⟨15,_⟩ => exact repair12347Cell15
  | ⟨16,_⟩ => exact repair12347Cell16
  | ⟨17,_⟩ => exact repair12347Cell17
  | ⟨18,_⟩ => exact repair12347Cell18
  | ⟨19,_⟩ => exact repair12347Cell19
  | ⟨20,_⟩ => exact repair12347Cell20
  | ⟨21,_⟩ => exact repair12347Cell21
  | ⟨22,_⟩ => exact repair12347Cell22
  | ⟨23,_⟩ => exact repair12347Cell23
  | ⟨24,_⟩ => exact repair12347Cell24
  | ⟨25,_⟩ => exact repair12347Cell25
  | ⟨26,_⟩ => exact repair12347Cell26
  | ⟨27,_⟩ => exact repair12347Cell27
  | ⟨28,_⟩ => exact repair12347Cell28
  | ⟨29,_⟩ => exact repair12347Cell29
  | ⟨30,_⟩ => exact repair12347Cell30
  | ⟨31,_⟩ => exact repair12347Cell31
  | ⟨32,_⟩ => exact repair12347Cell32
  | ⟨33,_⟩ => exact repair12347Cell33
  | ⟨34,_⟩ => exact repair12347Cell34
  | ⟨35,_⟩ => exact repair12347Cell35
  | ⟨36,_⟩ => exact repair12347Cell36
  | ⟨37,_⟩ => exact repair12347Cell37
  | ⟨38,_⟩ => exact repair12347Cell38
  | ⟨39,_⟩ => exact repair12347Cell39
  | ⟨40,_⟩ => exact repair12347Cell40
  | ⟨41,_⟩ => exact repair12347Cell41
  | ⟨42,_⟩ => exact repair12347Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12347 : FrameRepair 12347 scalarRow12347 where
  cap := cap12347
  cap_nonneg := fun j => (repair12347Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12347])
  endpoint := fun j => (repair12347Cells j).2.1
  endpoint_upper := fun j => (repair12347Cells j).2.2.1
  frame := fun j => (repair12347Cells j).2.2.2

noncomputable def cap12348 : Fin 43 → ℝ
  | ⟨0,_⟩ => (68985863 / 250000000 : ℝ)
  | ⟨1,_⟩ => (34543241 / 125000000 : ℝ)
  | ⟨2,_⟩ => (276747409 / 1000000000 : ℝ)
  | ⟨3,_⟩ => (138573947 / 500000000 : ℝ)
  | ⟨4,_⟩ => (27754739 / 100000000 : ℝ)
  | ⟨5,_⟩ => (34743237 / 125000000 : ℝ)
  | ⟨6,_⟩ => (278342943 / 1000000000 : ℝ)
  | ⟨7,_⟩ => (69684871 / 250000000 : ℝ)
  | ⟨8,_⟩ => (5582701 / 20000000 : ℝ)
  | ⟨9,_⟩ => (69882411 / 250000000 : ℝ)
  | ⟨10,_⟩ => (69980817 / 250000000 : ℝ)
  | ⟨11,_⟩ => (56063089 / 200000000 : ℝ)
  | ⟨12,_⟩ => (56141429 / 200000000 : ℝ)
  | ⟨13,_⟩ => (140548699 / 500000000 : ℝ)
  | ⟨14,_⟩ => (140743793 / 500000000 : ℝ)
  | ⟨15,_⟩ => (140938337 / 500000000 : ℝ)
  | ⟨16,_⟩ => (14113241 / 50000000 : ℝ)
  | ⟨17,_⟩ => (70663009 / 250000000 : ℝ)
  | ⟨18,_⟩ => (283038313 / 1000000000 : ℝ)
  | ⟨19,_⟩ => (141711831 / 500000000 : ℝ)
  | ⟨20,_⟩ => (56761617 / 200000000 : ℝ)
  | ⟨21,_⟩ => (284191593 / 1000000000 : ℝ)
  | ⟨22,_⟩ => (284574177 / 1000000000 : ℝ)
  | ⟨23,_⟩ => (284955351 / 1000000000 : ℝ)
  | ⟨24,_⟩ => (285336113 / 1000000000 : ℝ)
  | ⟨25,_⟩ => (57143103 / 200000000 : ℝ)
  | ⟨26,_⟩ => (286094513 / 1000000000 : ℝ)
  | ⟨27,_⟩ => (286472113 / 1000000000 : ℝ)
  | ⟨28,_⟩ => (17928051 / 62500000 : ℝ)
  | ⟨29,_⟩ => (2297797 / 8000000 : ℝ)
  | ⟨30,_⟩ => (287599041 / 1000000000 : ℝ)
  | ⟨31,_⟩ => (287973073 / 1000000000 : ℝ)
  | ⟨32,_⟩ => (11533849 / 40000000 : ℝ)
  | ⟨33,_⟩ => (72179497 / 250000000 : ℝ)
  | ⟨34,_⟩ => (72272219 / 250000000 : ℝ)
  | ⟨35,_⟩ => (144729447 / 500000000 : ℝ)
  | ⟨36,_⟩ => (57965607 / 200000000 : ℝ)
  | ⟨37,_⟩ => (290196317 / 1000000000 : ℝ)
  | ⟨38,_⟩ => (36320467 / 125000000 : ℝ)
  | ⟨39,_⟩ => (145464891 / 500000000 : ℝ)
  | ⟨40,_⟩ => (291294971 / 1000000000 : ℝ)
  | ⟨41,_⟩ => (72914827 / 250000000 : ℝ)
  | ⟨42,_⟩ => (58404559 / 200000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12348Cell0 :
    0 ≤ cap12348 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12348 (parameters ⟨0,by decide⟩)
      (scalarRow12348.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12348 ⟨0,by decide⟩ ∧
    (scalarRow12348.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12348 ⟨0,by decide⟩ + (scalarRow12348.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12348.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12348.targetFrame := by
  norm_num [cap12348, scalarRow12348, sourceIndex, cell12348, BstLean.Part263.envelope, parameters]

theorem repair12348Cell1 :
    0 ≤ cap12348 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12348 (parameters ⟨1,by decide⟩)
      (scalarRow12348.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12348 ⟨1,by decide⟩ ∧
    (scalarRow12348.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12348 ⟨1,by decide⟩ + (scalarRow12348.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12348.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12348.targetFrame := by
  norm_num [cap12348, scalarRow12348, sourceIndex, cell12348, BstLean.Part263.envelope, parameters]

theorem repair12348Cell2 :
    0 ≤ cap12348 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12348 (parameters ⟨2,by decide⟩)
      (scalarRow12348.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12348 ⟨2,by decide⟩ ∧
    (scalarRow12348.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12348 ⟨2,by decide⟩ + (scalarRow12348.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12348.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12348.targetFrame := by
  norm_num [cap12348, scalarRow12348, sourceIndex, cell12348, BstLean.Part263.envelope, parameters]

theorem repair12348Cell3 :
    0 ≤ cap12348 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12348 (parameters ⟨3,by decide⟩)
      (scalarRow12348.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12348 ⟨3,by decide⟩ ∧
    (scalarRow12348.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12348 ⟨3,by decide⟩ + (scalarRow12348.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12348.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12348.targetFrame := by
  norm_num [cap12348, scalarRow12348, sourceIndex, cell12348, BstLean.Part263.envelope, parameters]

theorem repair12348Cell4 :
    0 ≤ cap12348 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12348 (parameters ⟨4,by decide⟩)
      (scalarRow12348.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12348 ⟨4,by decide⟩ ∧
    (scalarRow12348.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12348 ⟨4,by decide⟩ + (scalarRow12348.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12348.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12348.targetFrame := by
  norm_num [cap12348, scalarRow12348, sourceIndex, cell12348, BstLean.Part263.envelope, parameters]

theorem repair12348Cell5 :
    0 ≤ cap12348 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12348 (parameters ⟨5,by decide⟩)
      (scalarRow12348.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12348 ⟨5,by decide⟩ ∧
    (scalarRow12348.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12348 ⟨5,by decide⟩ + (scalarRow12348.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12348.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12348.targetFrame := by
  norm_num [cap12348, scalarRow12348, sourceIndex, cell12348, BstLean.Part263.envelope, parameters]

theorem repair12348Cell6 :
    0 ≤ cap12348 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12348 (parameters ⟨6,by decide⟩)
      (scalarRow12348.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12348 ⟨6,by decide⟩ ∧
    (scalarRow12348.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12348 ⟨6,by decide⟩ + (scalarRow12348.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12348.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12348.targetFrame := by
  norm_num [cap12348, scalarRow12348, sourceIndex, cell12348, BstLean.Part263.envelope, parameters]

theorem repair12348Cell7 :
    0 ≤ cap12348 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12348 (parameters ⟨7,by decide⟩)
      (scalarRow12348.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12348 ⟨7,by decide⟩ ∧
    (scalarRow12348.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12348 ⟨7,by decide⟩ + (scalarRow12348.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12348.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12348.targetFrame := by
  norm_num [cap12348, scalarRow12348, sourceIndex, cell12348, BstLean.Part263.envelope, parameters]

theorem repair12348Cell8 :
    0 ≤ cap12348 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12348 (parameters ⟨8,by decide⟩)
      (scalarRow12348.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12348 ⟨8,by decide⟩ ∧
    (scalarRow12348.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12348 ⟨8,by decide⟩ + (scalarRow12348.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12348.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12348.targetFrame := by
  norm_num [cap12348, scalarRow12348, sourceIndex, cell12348, BstLean.Part263.envelope, parameters]

theorem repair12348Cell9 :
    0 ≤ cap12348 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12348 (parameters ⟨9,by decide⟩)
      (scalarRow12348.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12348 ⟨9,by decide⟩ ∧
    (scalarRow12348.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12348 ⟨9,by decide⟩ + (scalarRow12348.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12348.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12348.targetFrame := by
  norm_num [cap12348, scalarRow12348, sourceIndex, cell12348, BstLean.Part263.envelope, parameters]

theorem repair12348Cell10 :
    0 ≤ cap12348 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12348 (parameters ⟨10,by decide⟩)
      (scalarRow12348.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12348 ⟨10,by decide⟩ ∧
    (scalarRow12348.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12348 ⟨10,by decide⟩ + (scalarRow12348.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12348.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12348.targetFrame := by
  norm_num [cap12348, scalarRow12348, sourceIndex, cell12348, BstLean.Part263.envelope, parameters]

theorem repair12348Cell11 :
    0 ≤ cap12348 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12348 (parameters ⟨11,by decide⟩)
      (scalarRow12348.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12348 ⟨11,by decide⟩ ∧
    (scalarRow12348.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12348 ⟨11,by decide⟩ + (scalarRow12348.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12348.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12348.targetFrame := by
  norm_num [cap12348, scalarRow12348, sourceIndex, cell12348, BstLean.Part263.envelope, parameters]

theorem repair12348Cell12 :
    0 ≤ cap12348 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12348 (parameters ⟨12,by decide⟩)
      (scalarRow12348.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12348 ⟨12,by decide⟩ ∧
    (scalarRow12348.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12348 ⟨12,by decide⟩ + (scalarRow12348.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12348.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12348.targetFrame := by
  norm_num [cap12348, scalarRow12348, sourceIndex, cell12348, BstLean.Part263.envelope, parameters]

theorem repair12348Cell13 :
    0 ≤ cap12348 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12348 (parameters ⟨13,by decide⟩)
      (scalarRow12348.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12348 ⟨13,by decide⟩ ∧
    (scalarRow12348.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12348 ⟨13,by decide⟩ + (scalarRow12348.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12348.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12348.targetFrame := by
  norm_num [cap12348, scalarRow12348, sourceIndex, cell12348, BstLean.Part263.envelope, parameters]

theorem repair12348Cell14 :
    0 ≤ cap12348 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12348 (parameters ⟨14,by decide⟩)
      (scalarRow12348.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12348 ⟨14,by decide⟩ ∧
    (scalarRow12348.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12348 ⟨14,by decide⟩ + (scalarRow12348.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12348.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12348.targetFrame := by
  norm_num [cap12348, scalarRow12348, sourceIndex, cell12348, BstLean.Part263.envelope, parameters]

theorem repair12348Cell15 :
    0 ≤ cap12348 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12348 (parameters ⟨15,by decide⟩)
      (scalarRow12348.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12348 ⟨15,by decide⟩ ∧
    (scalarRow12348.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12348 ⟨15,by decide⟩ + (scalarRow12348.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12348.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12348.targetFrame := by
  norm_num [cap12348, scalarRow12348, sourceIndex, cell12348, BstLean.Part263.envelope, parameters]

theorem repair12348Cell16 :
    0 ≤ cap12348 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12348 (parameters ⟨16,by decide⟩)
      (scalarRow12348.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12348 ⟨16,by decide⟩ ∧
    (scalarRow12348.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12348 ⟨16,by decide⟩ + (scalarRow12348.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12348.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12348.targetFrame := by
  norm_num [cap12348, scalarRow12348, sourceIndex, cell12348, BstLean.Part263.envelope, parameters]

theorem repair12348Cell17 :
    0 ≤ cap12348 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12348 (parameters ⟨17,by decide⟩)
      (scalarRow12348.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12348 ⟨17,by decide⟩ ∧
    (scalarRow12348.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12348 ⟨17,by decide⟩ + (scalarRow12348.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12348.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12348.targetFrame := by
  norm_num [cap12348, scalarRow12348, sourceIndex, cell12348, BstLean.Part263.envelope, parameters]

theorem repair12348Cell18 :
    0 ≤ cap12348 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12348 (parameters ⟨18,by decide⟩)
      (scalarRow12348.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12348 ⟨18,by decide⟩ ∧
    (scalarRow12348.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12348 ⟨18,by decide⟩ + (scalarRow12348.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12348.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12348.targetFrame := by
  norm_num [cap12348, scalarRow12348, sourceIndex, cell12348, BstLean.Part263.envelope, parameters]

theorem repair12348Cell19 :
    0 ≤ cap12348 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12348 (parameters ⟨19,by decide⟩)
      (scalarRow12348.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12348 ⟨19,by decide⟩ ∧
    (scalarRow12348.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12348 ⟨19,by decide⟩ + (scalarRow12348.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12348.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12348.targetFrame := by
  norm_num [cap12348, scalarRow12348, sourceIndex, cell12348, BstLean.Part263.envelope, parameters]

theorem repair12348Cell20 :
    0 ≤ cap12348 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12348 (parameters ⟨20,by decide⟩)
      (scalarRow12348.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12348 ⟨20,by decide⟩ ∧
    (scalarRow12348.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12348 ⟨20,by decide⟩ + (scalarRow12348.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12348.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12348.targetFrame := by
  norm_num [cap12348, scalarRow12348, sourceIndex, cell12348, BstLean.Part263.envelope, parameters]

theorem repair12348Cell21 :
    0 ≤ cap12348 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12348 (parameters ⟨21,by decide⟩)
      (scalarRow12348.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12348 ⟨21,by decide⟩ ∧
    (scalarRow12348.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12348 ⟨21,by decide⟩ + (scalarRow12348.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12348.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12348.targetFrame := by
  norm_num [cap12348, scalarRow12348, sourceIndex, cell12348, BstLean.Part263.envelope, parameters]

theorem repair12348Cell22 :
    0 ≤ cap12348 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12348 (parameters ⟨22,by decide⟩)
      (scalarRow12348.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12348 ⟨22,by decide⟩ ∧
    (scalarRow12348.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12348 ⟨22,by decide⟩ + (scalarRow12348.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12348.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12348.targetFrame := by
  norm_num [cap12348, scalarRow12348, sourceIndex, cell12348, BstLean.Part263.envelope, parameters]

theorem repair12348Cell23 :
    0 ≤ cap12348 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12348 (parameters ⟨23,by decide⟩)
      (scalarRow12348.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12348 ⟨23,by decide⟩ ∧
    (scalarRow12348.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12348 ⟨23,by decide⟩ + (scalarRow12348.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12348.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12348.targetFrame := by
  norm_num [cap12348, scalarRow12348, sourceIndex, cell12348, BstLean.Part263.envelope, parameters]

theorem repair12348Cell24 :
    0 ≤ cap12348 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12348 (parameters ⟨24,by decide⟩)
      (scalarRow12348.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12348 ⟨24,by decide⟩ ∧
    (scalarRow12348.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12348 ⟨24,by decide⟩ + (scalarRow12348.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12348.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12348.targetFrame := by
  norm_num [cap12348, scalarRow12348, sourceIndex, cell12348, BstLean.Part263.envelope, parameters]

theorem repair12348Cell25 :
    0 ≤ cap12348 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12348 (parameters ⟨25,by decide⟩)
      (scalarRow12348.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12348 ⟨25,by decide⟩ ∧
    (scalarRow12348.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12348 ⟨25,by decide⟩ + (scalarRow12348.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12348.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12348.targetFrame := by
  norm_num [cap12348, scalarRow12348, sourceIndex, cell12348, BstLean.Part263.envelope, parameters]

theorem repair12348Cell26 :
    0 ≤ cap12348 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12348 (parameters ⟨26,by decide⟩)
      (scalarRow12348.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12348 ⟨26,by decide⟩ ∧
    (scalarRow12348.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12348 ⟨26,by decide⟩ + (scalarRow12348.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12348.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12348.targetFrame := by
  norm_num [cap12348, scalarRow12348, sourceIndex, cell12348, BstLean.Part263.envelope, parameters]

theorem repair12348Cell27 :
    0 ≤ cap12348 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12348 (parameters ⟨27,by decide⟩)
      (scalarRow12348.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12348 ⟨27,by decide⟩ ∧
    (scalarRow12348.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12348 ⟨27,by decide⟩ + (scalarRow12348.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12348.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12348.targetFrame := by
  norm_num [cap12348, scalarRow12348, sourceIndex, cell12348, BstLean.Part263.envelope, parameters]

theorem repair12348Cell28 :
    0 ≤ cap12348 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12348 (parameters ⟨28,by decide⟩)
      (scalarRow12348.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12348 ⟨28,by decide⟩ ∧
    (scalarRow12348.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12348 ⟨28,by decide⟩ + (scalarRow12348.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12348.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12348.targetFrame := by
  norm_num [cap12348, scalarRow12348, sourceIndex, cell12348, BstLean.Part263.envelope, parameters]

theorem repair12348Cell29 :
    0 ≤ cap12348 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12348 (parameters ⟨29,by decide⟩)
      (scalarRow12348.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12348 ⟨29,by decide⟩ ∧
    (scalarRow12348.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12348 ⟨29,by decide⟩ + (scalarRow12348.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12348.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12348.targetFrame := by
  norm_num [cap12348, scalarRow12348, sourceIndex, cell12348, BstLean.Part263.envelope, parameters]

theorem repair12348Cell30 :
    0 ≤ cap12348 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12348 (parameters ⟨30,by decide⟩)
      (scalarRow12348.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12348 ⟨30,by decide⟩ ∧
    (scalarRow12348.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12348 ⟨30,by decide⟩ + (scalarRow12348.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12348.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12348.targetFrame := by
  norm_num [cap12348, scalarRow12348, sourceIndex, cell12348, BstLean.Part263.envelope, parameters]

theorem repair12348Cell31 :
    0 ≤ cap12348 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12348 (parameters ⟨31,by decide⟩)
      (scalarRow12348.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12348 ⟨31,by decide⟩ ∧
    (scalarRow12348.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12348 ⟨31,by decide⟩ + (scalarRow12348.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12348.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12348.targetFrame := by
  norm_num [cap12348, scalarRow12348, sourceIndex, cell12348, BstLean.Part263.envelope, parameters]

theorem repair12348Cell32 :
    0 ≤ cap12348 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12348 (parameters ⟨32,by decide⟩)
      (scalarRow12348.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12348 ⟨32,by decide⟩ ∧
    (scalarRow12348.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12348 ⟨32,by decide⟩ + (scalarRow12348.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12348.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12348.targetFrame := by
  norm_num [cap12348, scalarRow12348, sourceIndex, cell12348, BstLean.Part263.envelope, parameters]

theorem repair12348Cell33 :
    0 ≤ cap12348 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12348 (parameters ⟨33,by decide⟩)
      (scalarRow12348.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12348 ⟨33,by decide⟩ ∧
    (scalarRow12348.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12348 ⟨33,by decide⟩ + (scalarRow12348.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12348.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12348.targetFrame := by
  norm_num [cap12348, scalarRow12348, sourceIndex, cell12348, BstLean.Part263.envelope, parameters]

theorem repair12348Cell34 :
    0 ≤ cap12348 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12348 (parameters ⟨34,by decide⟩)
      (scalarRow12348.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12348 ⟨34,by decide⟩ ∧
    (scalarRow12348.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12348 ⟨34,by decide⟩ + (scalarRow12348.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12348.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12348.targetFrame := by
  norm_num [cap12348, scalarRow12348, sourceIndex, cell12348, BstLean.Part263.envelope, parameters]

theorem repair12348Cell35 :
    0 ≤ cap12348 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12348 (parameters ⟨35,by decide⟩)
      (scalarRow12348.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12348 ⟨35,by decide⟩ ∧
    (scalarRow12348.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12348 ⟨35,by decide⟩ + (scalarRow12348.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12348.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12348.targetFrame := by
  norm_num [cap12348, scalarRow12348, sourceIndex, cell12348, BstLean.Part263.envelope, parameters]

theorem repair12348Cell36 :
    0 ≤ cap12348 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12348 (parameters ⟨36,by decide⟩)
      (scalarRow12348.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12348 ⟨36,by decide⟩ ∧
    (scalarRow12348.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12348 ⟨36,by decide⟩ + (scalarRow12348.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12348.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12348.targetFrame := by
  norm_num [cap12348, scalarRow12348, sourceIndex, cell12348, BstLean.Part263.envelope, parameters]

theorem repair12348Cell37 :
    0 ≤ cap12348 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12348 (parameters ⟨37,by decide⟩)
      (scalarRow12348.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12348 ⟨37,by decide⟩ ∧
    (scalarRow12348.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12348 ⟨37,by decide⟩ + (scalarRow12348.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12348.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12348.targetFrame := by
  norm_num [cap12348, scalarRow12348, sourceIndex, cell12348, BstLean.Part263.envelope, parameters]

theorem repair12348Cell38 :
    0 ≤ cap12348 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12348 (parameters ⟨38,by decide⟩)
      (scalarRow12348.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12348 ⟨38,by decide⟩ ∧
    (scalarRow12348.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12348 ⟨38,by decide⟩ + (scalarRow12348.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12348.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12348.targetFrame := by
  norm_num [cap12348, scalarRow12348, sourceIndex, cell12348, BstLean.Part263.envelope, parameters]

theorem repair12348Cell39 :
    0 ≤ cap12348 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12348 (parameters ⟨39,by decide⟩)
      (scalarRow12348.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12348 ⟨39,by decide⟩ ∧
    (scalarRow12348.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12348 ⟨39,by decide⟩ + (scalarRow12348.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12348.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12348.targetFrame := by
  norm_num [cap12348, scalarRow12348, sourceIndex, cell12348, BstLean.Part263.envelope, parameters]

theorem repair12348Cell40 :
    0 ≤ cap12348 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12348 (parameters ⟨40,by decide⟩)
      (scalarRow12348.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12348 ⟨40,by decide⟩ ∧
    (scalarRow12348.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12348 ⟨40,by decide⟩ + (scalarRow12348.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12348.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12348.targetFrame := by
  norm_num [cap12348, scalarRow12348, sourceIndex, cell12348, BstLean.Part263.envelope, parameters]

theorem repair12348Cell41 :
    0 ≤ cap12348 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12348 (parameters ⟨41,by decide⟩)
      (scalarRow12348.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12348 ⟨41,by decide⟩ ∧
    (scalarRow12348.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12348 ⟨41,by decide⟩ + (scalarRow12348.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12348.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12348.targetFrame := by
  norm_num [cap12348, scalarRow12348, sourceIndex, cell12348, BstLean.Part263.envelope, parameters]

theorem repair12348Cell42 :
    0 ≤ cap12348 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12348 (parameters ⟨42,by decide⟩)
      (scalarRow12348.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12348 ⟨42,by decide⟩ ∧
    (scalarRow12348.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12348 ⟨42,by decide⟩ + (scalarRow12348.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12348.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12348.targetFrame := by
  norm_num [cap12348, scalarRow12348, sourceIndex, cell12348, BstLean.Part263.envelope, parameters]

theorem repair12348Cells (j : Fin 43) :
    0 ≤ cap12348 j ∧
    BstLean.Part263.envelope 12348 (parameters j) (scalarRow12348.table (sourceIndex j)).upper ≤ cap12348 j ∧
    (scalarRow12348.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12348 j + (scalarRow12348.table (sourceIndex j)).centre) /
      (scalarRow12348.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12348.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12348Cell0
  | ⟨1,_⟩ => exact repair12348Cell1
  | ⟨2,_⟩ => exact repair12348Cell2
  | ⟨3,_⟩ => exact repair12348Cell3
  | ⟨4,_⟩ => exact repair12348Cell4
  | ⟨5,_⟩ => exact repair12348Cell5
  | ⟨6,_⟩ => exact repair12348Cell6
  | ⟨7,_⟩ => exact repair12348Cell7
  | ⟨8,_⟩ => exact repair12348Cell8
  | ⟨9,_⟩ => exact repair12348Cell9
  | ⟨10,_⟩ => exact repair12348Cell10
  | ⟨11,_⟩ => exact repair12348Cell11
  | ⟨12,_⟩ => exact repair12348Cell12
  | ⟨13,_⟩ => exact repair12348Cell13
  | ⟨14,_⟩ => exact repair12348Cell14
  | ⟨15,_⟩ => exact repair12348Cell15
  | ⟨16,_⟩ => exact repair12348Cell16
  | ⟨17,_⟩ => exact repair12348Cell17
  | ⟨18,_⟩ => exact repair12348Cell18
  | ⟨19,_⟩ => exact repair12348Cell19
  | ⟨20,_⟩ => exact repair12348Cell20
  | ⟨21,_⟩ => exact repair12348Cell21
  | ⟨22,_⟩ => exact repair12348Cell22
  | ⟨23,_⟩ => exact repair12348Cell23
  | ⟨24,_⟩ => exact repair12348Cell24
  | ⟨25,_⟩ => exact repair12348Cell25
  | ⟨26,_⟩ => exact repair12348Cell26
  | ⟨27,_⟩ => exact repair12348Cell27
  | ⟨28,_⟩ => exact repair12348Cell28
  | ⟨29,_⟩ => exact repair12348Cell29
  | ⟨30,_⟩ => exact repair12348Cell30
  | ⟨31,_⟩ => exact repair12348Cell31
  | ⟨32,_⟩ => exact repair12348Cell32
  | ⟨33,_⟩ => exact repair12348Cell33
  | ⟨34,_⟩ => exact repair12348Cell34
  | ⟨35,_⟩ => exact repair12348Cell35
  | ⟨36,_⟩ => exact repair12348Cell36
  | ⟨37,_⟩ => exact repair12348Cell37
  | ⟨38,_⟩ => exact repair12348Cell38
  | ⟨39,_⟩ => exact repair12348Cell39
  | ⟨40,_⟩ => exact repair12348Cell40
  | ⟨41,_⟩ => exact repair12348Cell41
  | ⟨42,_⟩ => exact repair12348Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12348 : FrameRepair 12348 scalarRow12348 where
  cap := cap12348
  cap_nonneg := fun j => (repair12348Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12348])
  endpoint := fun j => (repair12348Cells j).2.1
  endpoint_upper := fun j => (repair12348Cells j).2.2.1
  frame := fun j => (repair12348Cells j).2.2.2

noncomputable def cap12349 : Fin 43 → ℝ
  | ⟨0,_⟩ => (275943377 / 1000000000 : ℝ)
  | ⟨1,_⟩ => (138172923 / 500000000 : ℝ)
  | ⟨2,_⟩ => (138373661 / 500000000 : ℝ)
  | ⟨3,_⟩ => (1385739 / 5000000 : ℝ)
  | ⟨4,_⟩ => (277547289 / 1000000000 : ℝ)
  | ⟨5,_⟩ => (277945789 / 1000000000 : ℝ)
  | ⟨6,_⟩ => (278342829 / 1000000000 : ℝ)
  | ⟨7,_⟩ => (69684841 / 250000000 : ℝ)
  | ⟨8,_⟩ => (69783731 / 250000000 : ℝ)
  | ⟨9,_⟩ => (34941189 / 125000000 : ℝ)
  | ⟨10,_⟩ => (27992313 / 100000000 : ℝ)
  | ⟨11,_⟩ => (2803153 / 10000000 : ℝ)
  | ⟨12,_⟩ => (140353497 / 500000000 : ℝ)
  | ⟨13,_⟩ => (281097241 / 1000000000 : ℝ)
  | ⟨14,_⟩ => (140743711 / 500000000 : ℝ)
  | ⟨15,_⟩ => (35234563 / 125000000 : ℝ)
  | ⟨16,_⟩ => (70566161 / 250000000 : ℝ)
  | ⟨17,_⟩ => (282651853 / 1000000000 : ℝ)
  | ⟨18,_⟩ => (70759531 / 250000000 : ℝ)
  | ⟨19,_⟩ => (70855867 / 250000000 : ℝ)
  | ⟨20,_⟩ => (70951971 / 250000000 : ℝ)
  | ⟨21,_⟩ => (142095693 / 500000000 : ℝ)
  | ⟨22,_⟩ => (71143491 / 250000000 : ℝ)
  | ⟨23,_⟩ => (71238783 / 250000000 : ℝ)
  | ⟨24,_⟩ => (17833493 / 62500000 : ℝ)
  | ⟨25,_⟩ => (285715283 / 1000000000 : ℝ)
  | ⟨26,_⟩ => (11443771 / 40000000 : ℝ)
  | ⟨27,_⟩ => (286471869 / 1000000000 : ℝ)
  | ⟨28,_⟩ => (143424283 / 500000000 : ℝ)
  | ⟨29,_⟩ => (287224369 / 1000000000 : ℝ)
  | ⟨30,_⟩ => (287598779 / 1000000000 : ℝ)
  | ⟨31,_⟩ => (57594561 / 200000000 : ℝ)
  | ⟨32,_⟩ => (288345951 / 1000000000 : ℝ)
  | ⟨33,_⟩ => (72179427 / 250000000 : ℝ)
  | ⟨34,_⟩ => (28908859 / 100000000 : ℝ)
  | ⟨35,_⟩ => (144729301 / 500000000 : ℝ)
  | ⟨36,_⟩ => (289827737 / 1000000000 : ℝ)
  | ⟨37,_⟩ => (145098007 / 500000000 : ℝ)
  | ⟨38,_⟩ => (145281713 / 500000000 : ℝ)
  | ⟨39,_⟩ => (290929467 / 1000000000 : ℝ)
  | ⟨40,_⟩ => (291294649 / 1000000000 : ℝ)
  | ⟨41,_⟩ => (291658981 / 1000000000 : ℝ)
  | ⟨42,_⟩ => (292022461 / 1000000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12349Cell0 :
    0 ≤ cap12349 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12349 (parameters ⟨0,by decide⟩)
      (scalarRow12349.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12349 ⟨0,by decide⟩ ∧
    (scalarRow12349.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12349 ⟨0,by decide⟩ + (scalarRow12349.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12349.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12349.targetFrame := by
  norm_num [cap12349, scalarRow12349, sourceIndex, cell12349, BstLean.Part263.envelope, parameters]

theorem repair12349Cell1 :
    0 ≤ cap12349 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12349 (parameters ⟨1,by decide⟩)
      (scalarRow12349.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12349 ⟨1,by decide⟩ ∧
    (scalarRow12349.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12349 ⟨1,by decide⟩ + (scalarRow12349.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12349.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12349.targetFrame := by
  norm_num [cap12349, scalarRow12349, sourceIndex, cell12349, BstLean.Part263.envelope, parameters]

theorem repair12349Cell2 :
    0 ≤ cap12349 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12349 (parameters ⟨2,by decide⟩)
      (scalarRow12349.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12349 ⟨2,by decide⟩ ∧
    (scalarRow12349.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12349 ⟨2,by decide⟩ + (scalarRow12349.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12349.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12349.targetFrame := by
  norm_num [cap12349, scalarRow12349, sourceIndex, cell12349, BstLean.Part263.envelope, parameters]

theorem repair12349Cell3 :
    0 ≤ cap12349 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12349 (parameters ⟨3,by decide⟩)
      (scalarRow12349.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12349 ⟨3,by decide⟩ ∧
    (scalarRow12349.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12349 ⟨3,by decide⟩ + (scalarRow12349.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12349.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12349.targetFrame := by
  norm_num [cap12349, scalarRow12349, sourceIndex, cell12349, BstLean.Part263.envelope, parameters]

theorem repair12349Cell4 :
    0 ≤ cap12349 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12349 (parameters ⟨4,by decide⟩)
      (scalarRow12349.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12349 ⟨4,by decide⟩ ∧
    (scalarRow12349.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12349 ⟨4,by decide⟩ + (scalarRow12349.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12349.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12349.targetFrame := by
  norm_num [cap12349, scalarRow12349, sourceIndex, cell12349, BstLean.Part263.envelope, parameters]

theorem repair12349Cell5 :
    0 ≤ cap12349 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12349 (parameters ⟨5,by decide⟩)
      (scalarRow12349.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12349 ⟨5,by decide⟩ ∧
    (scalarRow12349.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12349 ⟨5,by decide⟩ + (scalarRow12349.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12349.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12349.targetFrame := by
  norm_num [cap12349, scalarRow12349, sourceIndex, cell12349, BstLean.Part263.envelope, parameters]

theorem repair12349Cell6 :
    0 ≤ cap12349 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12349 (parameters ⟨6,by decide⟩)
      (scalarRow12349.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12349 ⟨6,by decide⟩ ∧
    (scalarRow12349.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12349 ⟨6,by decide⟩ + (scalarRow12349.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12349.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12349.targetFrame := by
  norm_num [cap12349, scalarRow12349, sourceIndex, cell12349, BstLean.Part263.envelope, parameters]

theorem repair12349Cell7 :
    0 ≤ cap12349 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12349 (parameters ⟨7,by decide⟩)
      (scalarRow12349.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12349 ⟨7,by decide⟩ ∧
    (scalarRow12349.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12349 ⟨7,by decide⟩ + (scalarRow12349.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12349.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12349.targetFrame := by
  norm_num [cap12349, scalarRow12349, sourceIndex, cell12349, BstLean.Part263.envelope, parameters]

theorem repair12349Cell8 :
    0 ≤ cap12349 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12349 (parameters ⟨8,by decide⟩)
      (scalarRow12349.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12349 ⟨8,by decide⟩ ∧
    (scalarRow12349.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12349 ⟨8,by decide⟩ + (scalarRow12349.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12349.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12349.targetFrame := by
  norm_num [cap12349, scalarRow12349, sourceIndex, cell12349, BstLean.Part263.envelope, parameters]

theorem repair12349Cell9 :
    0 ≤ cap12349 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12349 (parameters ⟨9,by decide⟩)
      (scalarRow12349.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12349 ⟨9,by decide⟩ ∧
    (scalarRow12349.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12349 ⟨9,by decide⟩ + (scalarRow12349.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12349.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12349.targetFrame := by
  norm_num [cap12349, scalarRow12349, sourceIndex, cell12349, BstLean.Part263.envelope, parameters]

theorem repair12349Cell10 :
    0 ≤ cap12349 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12349 (parameters ⟨10,by decide⟩)
      (scalarRow12349.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12349 ⟨10,by decide⟩ ∧
    (scalarRow12349.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12349 ⟨10,by decide⟩ + (scalarRow12349.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12349.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12349.targetFrame := by
  norm_num [cap12349, scalarRow12349, sourceIndex, cell12349, BstLean.Part263.envelope, parameters]

theorem repair12349Cell11 :
    0 ≤ cap12349 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12349 (parameters ⟨11,by decide⟩)
      (scalarRow12349.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12349 ⟨11,by decide⟩ ∧
    (scalarRow12349.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12349 ⟨11,by decide⟩ + (scalarRow12349.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12349.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12349.targetFrame := by
  norm_num [cap12349, scalarRow12349, sourceIndex, cell12349, BstLean.Part263.envelope, parameters]

theorem repair12349Cell12 :
    0 ≤ cap12349 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12349 (parameters ⟨12,by decide⟩)
      (scalarRow12349.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12349 ⟨12,by decide⟩ ∧
    (scalarRow12349.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12349 ⟨12,by decide⟩ + (scalarRow12349.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12349.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12349.targetFrame := by
  norm_num [cap12349, scalarRow12349, sourceIndex, cell12349, BstLean.Part263.envelope, parameters]

theorem repair12349Cell13 :
    0 ≤ cap12349 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12349 (parameters ⟨13,by decide⟩)
      (scalarRow12349.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12349 ⟨13,by decide⟩ ∧
    (scalarRow12349.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12349 ⟨13,by decide⟩ + (scalarRow12349.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12349.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12349.targetFrame := by
  norm_num [cap12349, scalarRow12349, sourceIndex, cell12349, BstLean.Part263.envelope, parameters]

theorem repair12349Cell14 :
    0 ≤ cap12349 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12349 (parameters ⟨14,by decide⟩)
      (scalarRow12349.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12349 ⟨14,by decide⟩ ∧
    (scalarRow12349.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12349 ⟨14,by decide⟩ + (scalarRow12349.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12349.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12349.targetFrame := by
  norm_num [cap12349, scalarRow12349, sourceIndex, cell12349, BstLean.Part263.envelope, parameters]

theorem repair12349Cell15 :
    0 ≤ cap12349 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12349 (parameters ⟨15,by decide⟩)
      (scalarRow12349.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12349 ⟨15,by decide⟩ ∧
    (scalarRow12349.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12349 ⟨15,by decide⟩ + (scalarRow12349.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12349.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12349.targetFrame := by
  norm_num [cap12349, scalarRow12349, sourceIndex, cell12349, BstLean.Part263.envelope, parameters]

theorem repair12349Cell16 :
    0 ≤ cap12349 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12349 (parameters ⟨16,by decide⟩)
      (scalarRow12349.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12349 ⟨16,by decide⟩ ∧
    (scalarRow12349.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12349 ⟨16,by decide⟩ + (scalarRow12349.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12349.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12349.targetFrame := by
  norm_num [cap12349, scalarRow12349, sourceIndex, cell12349, BstLean.Part263.envelope, parameters]

theorem repair12349Cell17 :
    0 ≤ cap12349 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12349 (parameters ⟨17,by decide⟩)
      (scalarRow12349.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12349 ⟨17,by decide⟩ ∧
    (scalarRow12349.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12349 ⟨17,by decide⟩ + (scalarRow12349.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12349.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12349.targetFrame := by
  norm_num [cap12349, scalarRow12349, sourceIndex, cell12349, BstLean.Part263.envelope, parameters]

theorem repair12349Cell18 :
    0 ≤ cap12349 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12349 (parameters ⟨18,by decide⟩)
      (scalarRow12349.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12349 ⟨18,by decide⟩ ∧
    (scalarRow12349.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12349 ⟨18,by decide⟩ + (scalarRow12349.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12349.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12349.targetFrame := by
  norm_num [cap12349, scalarRow12349, sourceIndex, cell12349, BstLean.Part263.envelope, parameters]

theorem repair12349Cell19 :
    0 ≤ cap12349 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12349 (parameters ⟨19,by decide⟩)
      (scalarRow12349.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12349 ⟨19,by decide⟩ ∧
    (scalarRow12349.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12349 ⟨19,by decide⟩ + (scalarRow12349.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12349.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12349.targetFrame := by
  norm_num [cap12349, scalarRow12349, sourceIndex, cell12349, BstLean.Part263.envelope, parameters]

theorem repair12349Cell20 :
    0 ≤ cap12349 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12349 (parameters ⟨20,by decide⟩)
      (scalarRow12349.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12349 ⟨20,by decide⟩ ∧
    (scalarRow12349.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12349 ⟨20,by decide⟩ + (scalarRow12349.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12349.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12349.targetFrame := by
  norm_num [cap12349, scalarRow12349, sourceIndex, cell12349, BstLean.Part263.envelope, parameters]

theorem repair12349Cell21 :
    0 ≤ cap12349 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12349 (parameters ⟨21,by decide⟩)
      (scalarRow12349.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12349 ⟨21,by decide⟩ ∧
    (scalarRow12349.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12349 ⟨21,by decide⟩ + (scalarRow12349.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12349.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12349.targetFrame := by
  norm_num [cap12349, scalarRow12349, sourceIndex, cell12349, BstLean.Part263.envelope, parameters]

theorem repair12349Cell22 :
    0 ≤ cap12349 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12349 (parameters ⟨22,by decide⟩)
      (scalarRow12349.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12349 ⟨22,by decide⟩ ∧
    (scalarRow12349.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12349 ⟨22,by decide⟩ + (scalarRow12349.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12349.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12349.targetFrame := by
  norm_num [cap12349, scalarRow12349, sourceIndex, cell12349, BstLean.Part263.envelope, parameters]

theorem repair12349Cell23 :
    0 ≤ cap12349 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12349 (parameters ⟨23,by decide⟩)
      (scalarRow12349.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12349 ⟨23,by decide⟩ ∧
    (scalarRow12349.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12349 ⟨23,by decide⟩ + (scalarRow12349.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12349.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12349.targetFrame := by
  norm_num [cap12349, scalarRow12349, sourceIndex, cell12349, BstLean.Part263.envelope, parameters]

theorem repair12349Cell24 :
    0 ≤ cap12349 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12349 (parameters ⟨24,by decide⟩)
      (scalarRow12349.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12349 ⟨24,by decide⟩ ∧
    (scalarRow12349.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12349 ⟨24,by decide⟩ + (scalarRow12349.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12349.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12349.targetFrame := by
  norm_num [cap12349, scalarRow12349, sourceIndex, cell12349, BstLean.Part263.envelope, parameters]

theorem repair12349Cell25 :
    0 ≤ cap12349 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12349 (parameters ⟨25,by decide⟩)
      (scalarRow12349.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12349 ⟨25,by decide⟩ ∧
    (scalarRow12349.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12349 ⟨25,by decide⟩ + (scalarRow12349.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12349.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12349.targetFrame := by
  norm_num [cap12349, scalarRow12349, sourceIndex, cell12349, BstLean.Part263.envelope, parameters]

theorem repair12349Cell26 :
    0 ≤ cap12349 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12349 (parameters ⟨26,by decide⟩)
      (scalarRow12349.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12349 ⟨26,by decide⟩ ∧
    (scalarRow12349.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12349 ⟨26,by decide⟩ + (scalarRow12349.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12349.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12349.targetFrame := by
  norm_num [cap12349, scalarRow12349, sourceIndex, cell12349, BstLean.Part263.envelope, parameters]

theorem repair12349Cell27 :
    0 ≤ cap12349 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12349 (parameters ⟨27,by decide⟩)
      (scalarRow12349.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12349 ⟨27,by decide⟩ ∧
    (scalarRow12349.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12349 ⟨27,by decide⟩ + (scalarRow12349.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12349.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12349.targetFrame := by
  norm_num [cap12349, scalarRow12349, sourceIndex, cell12349, BstLean.Part263.envelope, parameters]

theorem repair12349Cell28 :
    0 ≤ cap12349 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12349 (parameters ⟨28,by decide⟩)
      (scalarRow12349.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12349 ⟨28,by decide⟩ ∧
    (scalarRow12349.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12349 ⟨28,by decide⟩ + (scalarRow12349.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12349.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12349.targetFrame := by
  norm_num [cap12349, scalarRow12349, sourceIndex, cell12349, BstLean.Part263.envelope, parameters]

theorem repair12349Cell29 :
    0 ≤ cap12349 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12349 (parameters ⟨29,by decide⟩)
      (scalarRow12349.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12349 ⟨29,by decide⟩ ∧
    (scalarRow12349.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12349 ⟨29,by decide⟩ + (scalarRow12349.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12349.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12349.targetFrame := by
  norm_num [cap12349, scalarRow12349, sourceIndex, cell12349, BstLean.Part263.envelope, parameters]

theorem repair12349Cell30 :
    0 ≤ cap12349 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12349 (parameters ⟨30,by decide⟩)
      (scalarRow12349.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12349 ⟨30,by decide⟩ ∧
    (scalarRow12349.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12349 ⟨30,by decide⟩ + (scalarRow12349.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12349.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12349.targetFrame := by
  norm_num [cap12349, scalarRow12349, sourceIndex, cell12349, BstLean.Part263.envelope, parameters]

theorem repair12349Cell31 :
    0 ≤ cap12349 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12349 (parameters ⟨31,by decide⟩)
      (scalarRow12349.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12349 ⟨31,by decide⟩ ∧
    (scalarRow12349.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12349 ⟨31,by decide⟩ + (scalarRow12349.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12349.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12349.targetFrame := by
  norm_num [cap12349, scalarRow12349, sourceIndex, cell12349, BstLean.Part263.envelope, parameters]

theorem repair12349Cell32 :
    0 ≤ cap12349 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12349 (parameters ⟨32,by decide⟩)
      (scalarRow12349.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12349 ⟨32,by decide⟩ ∧
    (scalarRow12349.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12349 ⟨32,by decide⟩ + (scalarRow12349.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12349.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12349.targetFrame := by
  norm_num [cap12349, scalarRow12349, sourceIndex, cell12349, BstLean.Part263.envelope, parameters]

theorem repair12349Cell33 :
    0 ≤ cap12349 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12349 (parameters ⟨33,by decide⟩)
      (scalarRow12349.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12349 ⟨33,by decide⟩ ∧
    (scalarRow12349.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12349 ⟨33,by decide⟩ + (scalarRow12349.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12349.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12349.targetFrame := by
  norm_num [cap12349, scalarRow12349, sourceIndex, cell12349, BstLean.Part263.envelope, parameters]

theorem repair12349Cell34 :
    0 ≤ cap12349 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12349 (parameters ⟨34,by decide⟩)
      (scalarRow12349.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12349 ⟨34,by decide⟩ ∧
    (scalarRow12349.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12349 ⟨34,by decide⟩ + (scalarRow12349.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12349.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12349.targetFrame := by
  norm_num [cap12349, scalarRow12349, sourceIndex, cell12349, BstLean.Part263.envelope, parameters]

theorem repair12349Cell35 :
    0 ≤ cap12349 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12349 (parameters ⟨35,by decide⟩)
      (scalarRow12349.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12349 ⟨35,by decide⟩ ∧
    (scalarRow12349.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12349 ⟨35,by decide⟩ + (scalarRow12349.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12349.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12349.targetFrame := by
  norm_num [cap12349, scalarRow12349, sourceIndex, cell12349, BstLean.Part263.envelope, parameters]

theorem repair12349Cell36 :
    0 ≤ cap12349 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12349 (parameters ⟨36,by decide⟩)
      (scalarRow12349.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12349 ⟨36,by decide⟩ ∧
    (scalarRow12349.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12349 ⟨36,by decide⟩ + (scalarRow12349.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12349.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12349.targetFrame := by
  norm_num [cap12349, scalarRow12349, sourceIndex, cell12349, BstLean.Part263.envelope, parameters]

theorem repair12349Cell37 :
    0 ≤ cap12349 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12349 (parameters ⟨37,by decide⟩)
      (scalarRow12349.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12349 ⟨37,by decide⟩ ∧
    (scalarRow12349.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12349 ⟨37,by decide⟩ + (scalarRow12349.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12349.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12349.targetFrame := by
  norm_num [cap12349, scalarRow12349, sourceIndex, cell12349, BstLean.Part263.envelope, parameters]

theorem repair12349Cell38 :
    0 ≤ cap12349 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12349 (parameters ⟨38,by decide⟩)
      (scalarRow12349.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12349 ⟨38,by decide⟩ ∧
    (scalarRow12349.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12349 ⟨38,by decide⟩ + (scalarRow12349.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12349.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12349.targetFrame := by
  norm_num [cap12349, scalarRow12349, sourceIndex, cell12349, BstLean.Part263.envelope, parameters]

theorem repair12349Cell39 :
    0 ≤ cap12349 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12349 (parameters ⟨39,by decide⟩)
      (scalarRow12349.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12349 ⟨39,by decide⟩ ∧
    (scalarRow12349.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12349 ⟨39,by decide⟩ + (scalarRow12349.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12349.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12349.targetFrame := by
  norm_num [cap12349, scalarRow12349, sourceIndex, cell12349, BstLean.Part263.envelope, parameters]

theorem repair12349Cell40 :
    0 ≤ cap12349 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12349 (parameters ⟨40,by decide⟩)
      (scalarRow12349.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12349 ⟨40,by decide⟩ ∧
    (scalarRow12349.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12349 ⟨40,by decide⟩ + (scalarRow12349.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12349.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12349.targetFrame := by
  norm_num [cap12349, scalarRow12349, sourceIndex, cell12349, BstLean.Part263.envelope, parameters]

theorem repair12349Cell41 :
    0 ≤ cap12349 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12349 (parameters ⟨41,by decide⟩)
      (scalarRow12349.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12349 ⟨41,by decide⟩ ∧
    (scalarRow12349.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12349 ⟨41,by decide⟩ + (scalarRow12349.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12349.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12349.targetFrame := by
  norm_num [cap12349, scalarRow12349, sourceIndex, cell12349, BstLean.Part263.envelope, parameters]

theorem repair12349Cell42 :
    0 ≤ cap12349 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12349 (parameters ⟨42,by decide⟩)
      (scalarRow12349.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12349 ⟨42,by decide⟩ ∧
    (scalarRow12349.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12349 ⟨42,by decide⟩ + (scalarRow12349.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12349.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12349.targetFrame := by
  norm_num [cap12349, scalarRow12349, sourceIndex, cell12349, BstLean.Part263.envelope, parameters]

theorem repair12349Cells (j : Fin 43) :
    0 ≤ cap12349 j ∧
    BstLean.Part263.envelope 12349 (parameters j) (scalarRow12349.table (sourceIndex j)).upper ≤ cap12349 j ∧
    (scalarRow12349.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12349 j + (scalarRow12349.table (sourceIndex j)).centre) /
      (scalarRow12349.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12349.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12349Cell0
  | ⟨1,_⟩ => exact repair12349Cell1
  | ⟨2,_⟩ => exact repair12349Cell2
  | ⟨3,_⟩ => exact repair12349Cell3
  | ⟨4,_⟩ => exact repair12349Cell4
  | ⟨5,_⟩ => exact repair12349Cell5
  | ⟨6,_⟩ => exact repair12349Cell6
  | ⟨7,_⟩ => exact repair12349Cell7
  | ⟨8,_⟩ => exact repair12349Cell8
  | ⟨9,_⟩ => exact repair12349Cell9
  | ⟨10,_⟩ => exact repair12349Cell10
  | ⟨11,_⟩ => exact repair12349Cell11
  | ⟨12,_⟩ => exact repair12349Cell12
  | ⟨13,_⟩ => exact repair12349Cell13
  | ⟨14,_⟩ => exact repair12349Cell14
  | ⟨15,_⟩ => exact repair12349Cell15
  | ⟨16,_⟩ => exact repair12349Cell16
  | ⟨17,_⟩ => exact repair12349Cell17
  | ⟨18,_⟩ => exact repair12349Cell18
  | ⟨19,_⟩ => exact repair12349Cell19
  | ⟨20,_⟩ => exact repair12349Cell20
  | ⟨21,_⟩ => exact repair12349Cell21
  | ⟨22,_⟩ => exact repair12349Cell22
  | ⟨23,_⟩ => exact repair12349Cell23
  | ⟨24,_⟩ => exact repair12349Cell24
  | ⟨25,_⟩ => exact repair12349Cell25
  | ⟨26,_⟩ => exact repair12349Cell26
  | ⟨27,_⟩ => exact repair12349Cell27
  | ⟨28,_⟩ => exact repair12349Cell28
  | ⟨29,_⟩ => exact repair12349Cell29
  | ⟨30,_⟩ => exact repair12349Cell30
  | ⟨31,_⟩ => exact repair12349Cell31
  | ⟨32,_⟩ => exact repair12349Cell32
  | ⟨33,_⟩ => exact repair12349Cell33
  | ⟨34,_⟩ => exact repair12349Cell34
  | ⟨35,_⟩ => exact repair12349Cell35
  | ⟨36,_⟩ => exact repair12349Cell36
  | ⟨37,_⟩ => exact repair12349Cell37
  | ⟨38,_⟩ => exact repair12349Cell38
  | ⟨39,_⟩ => exact repair12349Cell39
  | ⟨40,_⟩ => exact repair12349Cell40
  | ⟨41,_⟩ => exact repair12349Cell41
  | ⟨42,_⟩ => exact repair12349Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12349 : FrameRepair 12349 scalarRow12349 where
  cap := cap12349
  cap_nonneg := fun j => (repair12349Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12349])
  endpoint := fun j => (repair12349Cells j).2.1
  endpoint_upper := fun j => (repair12349Cells j).2.2.1
  frame := fun j => (repair12349Cells j).2.2.2


end BstLean.Part264
