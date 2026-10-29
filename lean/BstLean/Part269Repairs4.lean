import BstLean.Part269Rows4
import BstLean.Part269RepairCommon
namespace BstLean.Part269
open Real Set BstLean.Part255 BstLean.Part263 BstLean.Part264
theorem repair12450Cells (j : Fin 43) :
    0 ≤ (scalarRow12450.table (sourceIndex j)).upper ∧
    (scalarRow12450.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12450.table (sourceIndex j)).centre) /
      (scalarRow12450.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12450.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12450,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12450,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12450,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12450,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12450,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12450,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12450,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12450,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12450,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12450,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12450,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12450,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12450,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12450,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12450,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12450,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12450,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12450,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12450,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12450,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12450,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12450,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12450,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12450,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12450,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12450,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12450,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12450,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12450,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12450,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12450,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12450,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12450,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12450,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12450,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12450,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12450,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12450,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12450,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12450,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12450,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12450,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12450,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12450,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12450,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12450,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12450,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12450,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12450,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12450,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12450,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12450,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12450,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12450,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12450,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12450,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12450,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12450,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12450,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12450,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12450,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12450,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12450,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12450,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12450,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12450,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12450,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12450,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12450,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12450,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12450,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12450,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12450,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12450,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12450,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12450,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12450,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12450,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12450,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12450,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12450,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12450,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12450,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12450,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12450,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12450,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12450 : FrameRepair 12450 scalarRow12450 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12450Cells j).1 (repair12450Cells j).2.1
  endpoint_upper := fun j => ((repair12450Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12450Cells j).2.2

theorem repair12451Cells (j : Fin 43) :
    0 ≤ (scalarRow12451.table (sourceIndex j)).upper ∧
    (scalarRow12451.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12451.table (sourceIndex j)).centre) /
      (scalarRow12451.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12451.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12451,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12451,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12451,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12451,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12451,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12451,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12451,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12451,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12451,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12451,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12451,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12451,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12451,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12451,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12451,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12451,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12451,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12451,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12451,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12451,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12451,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12451,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12451,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12451,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12451,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12451,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12451,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12451,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12451,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12451,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12451,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12451,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12451,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12451,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12451,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12451,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12451,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12451,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12451,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12451,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12451,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12451,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12451,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12451,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12451,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12451,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12451,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12451,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12451,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12451,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12451,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12451,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12451,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12451,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12451,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12451,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12451,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12451,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12451,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12451,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12451,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12451,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12451,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12451,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12451,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12451,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12451,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12451,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12451,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12451,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12451,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12451,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12451,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12451,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12451,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12451,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12451,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12451,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12451,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12451,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12451,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12451,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12451,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12451,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12451,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12451,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12451 : FrameRepair 12451 scalarRow12451 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12451Cells j).1 (repair12451Cells j).2.1
  endpoint_upper := fun j => ((repair12451Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12451Cells j).2.2

theorem repair12452Cells (j : Fin 43) :
    0 ≤ (scalarRow12452.table (sourceIndex j)).upper ∧
    (scalarRow12452.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12452.table (sourceIndex j)).centre) /
      (scalarRow12452.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12452.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12452,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12452,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12452,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12452,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12452,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12452,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12452,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12452,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12452,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12452,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12452,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12452,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12452,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12452,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12452,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12452,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12452,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12452,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12452,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12452,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12452,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12452,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12452,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12452,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12452,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12452,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12452,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12452,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12452,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12452,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12452,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12452,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12452,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12452,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12452,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12452,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12452,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12452,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12452,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12452,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12452,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12452,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12452,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12452,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12452,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12452,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12452,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12452,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12452,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12452,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12452,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12452,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12452,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12452,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12452,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12452,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12452,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12452,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12452,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12452,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12452,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12452,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12452,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12452,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12452,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12452,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12452,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12452,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12452,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12452,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12452,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12452,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12452,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12452,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12452,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12452,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12452,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12452,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12452,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12452,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12452,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12452,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12452,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12452,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12452,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12452,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12452 : FrameRepair 12452 scalarRow12452 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12452Cells j).1 (repair12452Cells j).2.1
  endpoint_upper := fun j => ((repair12452Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12452Cells j).2.2

theorem repair12453Cells (j : Fin 43) :
    0 ≤ (scalarRow12453.table (sourceIndex j)).upper ∧
    (scalarRow12453.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12453.table (sourceIndex j)).centre) /
      (scalarRow12453.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12453.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12453,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12453,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12453,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12453,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12453,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12453,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12453,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12453,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12453,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12453,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12453,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12453,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12453,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12453,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12453,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12453,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12453,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12453,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12453,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12453,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12453,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12453,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12453,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12453,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12453,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12453,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12453,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12453,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12453,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12453,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12453,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12453,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12453,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12453,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12453,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12453,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12453,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12453,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12453,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12453,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12453,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12453,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12453,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12453,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12453,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12453,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12453,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12453,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12453,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12453,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12453,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12453,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12453,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12453,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12453,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12453,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12453,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12453,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12453,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12453,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12453,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12453,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12453,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12453,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12453,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12453,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12453,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12453,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12453,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12453,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12453,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12453,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12453,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12453,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12453,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12453,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12453,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12453,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12453,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12453,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12453,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12453,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12453,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12453,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12453,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12453,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12453 : FrameRepair 12453 scalarRow12453 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12453Cells j).1 (repair12453Cells j).2.1
  endpoint_upper := fun j => ((repair12453Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12453Cells j).2.2

theorem repair12454Cells (j : Fin 43) :
    0 ≤ (scalarRow12454.table (sourceIndex j)).upper ∧
    (scalarRow12454.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12454.table (sourceIndex j)).centre) /
      (scalarRow12454.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12454.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12454,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12454,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12454,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12454,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12454,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12454,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12454,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12454,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12454,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12454,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12454,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12454,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12454,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12454,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12454,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12454,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12454,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12454,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12454,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12454,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12454,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12454,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12454,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12454,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12454,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12454,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12454,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12454,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12454,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12454,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12454,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12454,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12454,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12454,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12454,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12454,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12454,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12454,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12454,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12454,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12454,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12454,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12454,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12454,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12454,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12454,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12454,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12454,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12454,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12454,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12454,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12454,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12454,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12454,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12454,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12454,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12454,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12454,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12454,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12454,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12454,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12454,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12454,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12454,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12454,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12454,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12454,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12454,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12454,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12454,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12454,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12454,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12454,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12454,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12454,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12454,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12454,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12454,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12454,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12454,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12454,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12454,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12454,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12454,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12454,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12454,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12454 : FrameRepair 12454 scalarRow12454 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12454Cells j).1 (repair12454Cells j).2.1
  endpoint_upper := fun j => ((repair12454Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12454Cells j).2.2

theorem repair12455Cells (j : Fin 43) :
    0 ≤ (scalarRow12455.table (sourceIndex j)).upper ∧
    (scalarRow12455.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12455.table (sourceIndex j)).centre) /
      (scalarRow12455.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12455.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12455,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12455,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12455,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12455,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12455,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12455,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12455,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12455,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12455,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12455,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12455,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12455,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12455,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12455,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12455,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12455,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12455,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12455,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12455,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12455,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12455,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12455,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12455,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12455,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12455,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12455,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12455,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12455,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12455,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12455,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12455,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12455,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12455,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12455,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12455,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12455,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12455,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12455,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12455,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12455,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12455,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12455,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12455,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12455,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12455,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12455,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12455,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12455,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12455,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12455,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12455,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12455,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12455,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12455,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12455,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12455,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12455,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12455,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12455,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12455,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12455,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12455,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12455,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12455,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12455,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12455,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12455,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12455,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12455,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12455,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12455,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12455,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12455,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12455,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12455,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12455,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12455,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12455,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12455,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12455,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12455,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12455,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12455,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12455,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12455,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12455,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12455 : FrameRepair 12455 scalarRow12455 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12455Cells j).1 (repair12455Cells j).2.1
  endpoint_upper := fun j => ((repair12455Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12455Cells j).2.2

theorem repair12456Cells (j : Fin 43) :
    0 ≤ (scalarRow12456.table (sourceIndex j)).upper ∧
    (scalarRow12456.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12456.table (sourceIndex j)).centre) /
      (scalarRow12456.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12456.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12456,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12456,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12456,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12456,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12456,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12456,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12456,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12456,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12456,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12456,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12456,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12456,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12456,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12456,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12456,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12456,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12456,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12456,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12456,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12456,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12456,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12456,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12456,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12456,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12456,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12456,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12456,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12456,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12456,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12456,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12456,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12456,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12456,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12456,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12456,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12456,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12456,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12456,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12456,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12456,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12456,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12456,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12456,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12456,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12456,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12456,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12456,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12456,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12456,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12456,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12456,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12456,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12456,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12456,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12456,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12456,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12456,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12456,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12456,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12456,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12456,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12456,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12456,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12456,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12456,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12456,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12456,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12456,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12456,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12456,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12456,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12456,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12456,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12456,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12456,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12456,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12456,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12456,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12456,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12456,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12456,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12456,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12456,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12456,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12456,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12456,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12456 : FrameRepair 12456 scalarRow12456 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12456Cells j).1 (repair12456Cells j).2.1
  endpoint_upper := fun j => ((repair12456Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12456Cells j).2.2

theorem repair12457Cells (j : Fin 43) :
    0 ≤ (scalarRow12457.table (sourceIndex j)).upper ∧
    (scalarRow12457.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12457.table (sourceIndex j)).centre) /
      (scalarRow12457.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12457.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12457,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12457,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12457,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12457,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12457,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12457,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12457,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12457,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12457,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12457,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12457,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12457,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12457,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12457,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12457,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12457,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12457,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12457,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12457,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12457,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12457,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12457,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12457,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12457,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12457,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12457,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12457,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12457,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12457,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12457,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12457,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12457,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12457,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12457,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12457,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12457,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12457,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12457,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12457,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12457,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12457,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12457,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12457,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12457,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12457,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12457,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12457,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12457,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12457,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12457,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12457,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12457,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12457,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12457,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12457,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12457,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12457,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12457,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12457,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12457,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12457,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12457,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12457,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12457,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12457,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12457,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12457,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12457,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12457,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12457,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12457,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12457,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12457,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12457,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12457,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12457,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12457,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12457,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12457,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12457,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12457,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12457,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12457,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12457,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12457,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12457,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12457 : FrameRepair 12457 scalarRow12457 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12457Cells j).1 (repair12457Cells j).2.1
  endpoint_upper := fun j => ((repair12457Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12457Cells j).2.2

theorem repair12458Cells (j : Fin 43) :
    0 ≤ (scalarRow12458.table (sourceIndex j)).upper ∧
    (scalarRow12458.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12458.table (sourceIndex j)).centre) /
      (scalarRow12458.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12458.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12458,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12458,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12458,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12458,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12458,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12458,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12458,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12458,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12458,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12458,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12458,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12458,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12458,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12458,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12458,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12458,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12458,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12458,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12458,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12458,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12458,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12458,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12458,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12458,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12458,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12458,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12458,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12458,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12458,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12458,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12458,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12458,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12458,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12458,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12458,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12458,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12458,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12458,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12458,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12458,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12458,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12458,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12458,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12458,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12458,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12458,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12458,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12458,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12458,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12458,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12458,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12458,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12458,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12458,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12458,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12458,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12458,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12458,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12458,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12458,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12458,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12458,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12458,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12458,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12458,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12458,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12458,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12458,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12458,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12458,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12458,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12458,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12458,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12458,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12458,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12458,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12458,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12458,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12458,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12458,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12458,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12458,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12458,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12458,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12458,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12458,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12458 : FrameRepair 12458 scalarRow12458 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12458Cells j).1 (repair12458Cells j).2.1
  endpoint_upper := fun j => ((repair12458Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12458Cells j).2.2

theorem repair12459Cells (j : Fin 43) :
    0 ≤ (scalarRow12459.table (sourceIndex j)).upper ∧
    (scalarRow12459.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12459.table (sourceIndex j)).centre) /
      (scalarRow12459.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12459.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12459,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12459,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12459,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12459,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12459,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12459,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12459,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12459,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12459,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12459,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12459,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12459,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12459,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12459,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12459,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12459,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12459,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12459,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12459,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12459,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12459,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12459,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12459,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12459,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12459,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12459,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12459,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12459,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12459,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12459,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12459,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12459,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12459,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12459,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12459,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12459,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12459,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12459,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12459,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12459,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12459,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12459,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12459,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12459,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12459,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12459,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12459,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12459,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12459,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12459,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12459,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12459,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12459,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12459,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12459,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12459,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12459,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12459,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12459,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12459,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12459,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12459,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12459,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12459,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12459,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12459,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12459,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12459,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12459,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12459,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12459,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12459,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12459,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12459,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12459,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12459,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12459,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12459,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12459,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12459,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12459,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12459,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12459,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12459,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12459,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12459,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12459 : FrameRepair 12459 scalarRow12459 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12459Cells j).1 (repair12459Cells j).2.1
  endpoint_upper := fun j => ((repair12459Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12459Cells j).2.2

theorem repair12460Cells (j : Fin 43) :
    0 ≤ (scalarRow12460.table (sourceIndex j)).upper ∧
    (scalarRow12460.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12460.table (sourceIndex j)).centre) /
      (scalarRow12460.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12460.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12460,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12460,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12460,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12460,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12460,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12460,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12460,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12460,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12460,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12460,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12460,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12460,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12460,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12460,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12460,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12460,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12460,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12460,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12460,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12460,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12460,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12460,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12460,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12460,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12460,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12460,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12460,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12460,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12460,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12460,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12460,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12460,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12460,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12460,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12460,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12460,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12460,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12460,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12460,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12460,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12460,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12460,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12460,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12460,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12460,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12460,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12460,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12460,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12460,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12460,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12460,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12460,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12460,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12460,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12460,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12460,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12460,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12460,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12460,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12460,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12460,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12460,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12460,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12460,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12460,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12460,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12460,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12460,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12460,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12460,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12460,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12460,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12460,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12460,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12460,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12460,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12460,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12460,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12460,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12460,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12460,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12460,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12460,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12460,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12460,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12460,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12460 : FrameRepair 12460 scalarRow12460 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12460Cells j).1 (repair12460Cells j).2.1
  endpoint_upper := fun j => ((repair12460Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12460Cells j).2.2

theorem repair12461Cells (j : Fin 43) :
    0 ≤ (scalarRow12461.table (sourceIndex j)).upper ∧
    (scalarRow12461.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12461.table (sourceIndex j)).centre) /
      (scalarRow12461.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12461.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12461,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12461,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12461,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12461,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12461,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12461,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12461,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12461,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12461,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12461,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12461,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12461,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12461,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12461,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12461,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12461,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12461,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12461,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12461,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12461,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12461,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12461,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12461,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12461,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12461,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12461,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12461,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12461,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12461,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12461,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12461,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12461,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12461,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12461,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12461,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12461,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12461,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12461,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12461,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12461,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12461,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12461,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12461,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12461,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12461,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12461,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12461,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12461,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12461,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12461,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12461,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12461,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12461,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12461,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12461,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12461,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12461,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12461,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12461,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12461,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12461,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12461,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12461,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12461,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12461,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12461,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12461,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12461,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12461,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12461,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12461,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12461,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12461,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12461,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12461,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12461,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12461,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12461,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12461,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12461,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12461,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12461,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12461,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12461,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12461,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12461,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12461 : FrameRepair 12461 scalarRow12461 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12461Cells j).1 (repair12461Cells j).2.1
  endpoint_upper := fun j => ((repair12461Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12461Cells j).2.2

theorem repair12462Cells (j : Fin 43) :
    0 ≤ (scalarRow12462.table (sourceIndex j)).upper ∧
    (scalarRow12462.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12462.table (sourceIndex j)).centre) /
      (scalarRow12462.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12462.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12462,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12462,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12462,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12462,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12462,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12462,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12462,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12462,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12462,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12462,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12462,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12462,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12462,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12462,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12462,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12462,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12462,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12462,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12462,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12462,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12462,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12462,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12462,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12462,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12462,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12462,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12462,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12462,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12462,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12462,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12462,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12462,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12462,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12462,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12462,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12462,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12462,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12462,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12462,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12462,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12462,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12462,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12462,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12462,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12462,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12462,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12462,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12462,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12462,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12462,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12462,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12462,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12462,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12462,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12462,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12462,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12462,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12462,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12462,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12462,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12462,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12462,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12462,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12462,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12462,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12462,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12462,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12462,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12462,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12462,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12462,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12462,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12462,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12462,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12462,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12462,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12462,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12462,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12462,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12462,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12462,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12462,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12462,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12462,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12462,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12462,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12462 : FrameRepair 12462 scalarRow12462 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12462Cells j).1 (repair12462Cells j).2.1
  endpoint_upper := fun j => ((repair12462Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12462Cells j).2.2

theorem repair12463Cells (j : Fin 43) :
    0 ≤ (scalarRow12463.table (sourceIndex j)).upper ∧
    (scalarRow12463.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12463.table (sourceIndex j)).centre) /
      (scalarRow12463.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12463.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12463,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12463,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12463,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12463,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12463,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12463,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12463,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12463,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12463,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12463,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12463,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12463,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12463,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12463,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12463,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12463,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12463,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12463,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12463,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12463,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12463,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12463,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12463,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12463,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12463,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12463,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12463,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12463,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12463,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12463,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12463,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12463,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12463,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12463,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12463,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12463,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12463,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12463,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12463,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12463,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12463,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12463,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12463,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12463,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12463,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12463,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12463,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12463,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12463,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12463,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12463,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12463,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12463,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12463,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12463,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12463,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12463,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12463,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12463,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12463,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12463,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12463,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12463,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12463,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12463,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12463,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12463,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12463,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12463,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12463,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12463,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12463,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12463,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12463,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12463,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12463,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12463,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12463,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12463,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12463,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12463,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12463,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12463,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12463,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12463,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12463,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12463 : FrameRepair 12463 scalarRow12463 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12463Cells j).1 (repair12463Cells j).2.1
  endpoint_upper := fun j => ((repair12463Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12463Cells j).2.2

theorem repair12464Cells (j : Fin 43) :
    0 ≤ (scalarRow12464.table (sourceIndex j)).upper ∧
    (scalarRow12464.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12464.table (sourceIndex j)).centre) /
      (scalarRow12464.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12464.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12464,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12464,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12464,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12464,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12464,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12464,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12464,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12464,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12464,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12464,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12464,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12464,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12464,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12464,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12464,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12464,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12464,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12464,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12464,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12464,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12464,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12464,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12464,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12464,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12464,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12464,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12464,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12464,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12464,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12464,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12464,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12464,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12464,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12464,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12464,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12464,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12464,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12464,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12464,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12464,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12464,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12464,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12464,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12464,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12464,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12464,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12464,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12464,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12464,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12464,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12464,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12464,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12464,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12464,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12464,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12464,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12464,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12464,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12464,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12464,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12464,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12464,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12464,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12464,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12464,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12464,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12464,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12464,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12464,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12464,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12464,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12464,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12464,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12464,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12464,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12464,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12464,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12464,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12464,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12464,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12464,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12464,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12464,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12464,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12464,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12464,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12464 : FrameRepair 12464 scalarRow12464 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12464Cells j).1 (repair12464Cells j).2.1
  endpoint_upper := fun j => ((repair12464Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12464Cells j).2.2

theorem repair12465Cells (j : Fin 43) :
    0 ≤ (scalarRow12465.table (sourceIndex j)).upper ∧
    (scalarRow12465.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12465.table (sourceIndex j)).centre) /
      (scalarRow12465.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12465.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12465,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12465,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12465,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12465,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12465,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12465,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12465,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12465,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12465,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12465,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12465,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12465,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12465,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12465,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12465,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12465,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12465,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12465,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12465,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12465,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12465,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12465,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12465,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12465,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12465,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12465,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12465,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12465,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12465,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12465,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12465,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12465,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12465,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12465,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12465,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12465,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12465,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12465,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12465,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12465,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12465,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12465,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12465,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12465,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12465,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12465,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12465,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12465,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12465,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12465,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12465,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12465,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12465,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12465,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12465,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12465,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12465,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12465,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12465,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12465,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12465,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12465,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12465,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12465,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12465,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12465,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12465,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12465,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12465,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12465,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12465,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12465,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12465,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12465,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12465,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12465,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12465,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12465,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12465,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12465,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12465,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12465,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12465,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12465,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12465,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12465,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12465 : FrameRepair 12465 scalarRow12465 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12465Cells j).1 (repair12465Cells j).2.1
  endpoint_upper := fun j => ((repair12465Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12465Cells j).2.2

theorem repair12466Cells (j : Fin 43) :
    0 ≤ (scalarRow12466.table (sourceIndex j)).upper ∧
    (scalarRow12466.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12466.table (sourceIndex j)).centre) /
      (scalarRow12466.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12466.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12466,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12466,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12466,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12466,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12466,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12466,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12466,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12466,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12466,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12466,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12466,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12466,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12466,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12466,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12466,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12466,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12466,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12466,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12466,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12466,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12466,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12466,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12466,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12466,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12466,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12466,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12466,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12466,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12466,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12466,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12466,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12466,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12466,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12466,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12466,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12466,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12466,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12466,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12466,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12466,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12466,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12466,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12466,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12466,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12466,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12466,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12466,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12466,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12466,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12466,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12466,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12466,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12466,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12466,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12466,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12466,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12466,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12466,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12466,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12466,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12466,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12466,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12466,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12466,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12466,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12466,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12466,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12466,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12466,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12466,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12466,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12466,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12466,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12466,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12466,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12466,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12466,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12466,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12466,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12466,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12466,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12466,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12466,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12466,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12466,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12466,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12466 : FrameRepair 12466 scalarRow12466 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12466Cells j).1 (repair12466Cells j).2.1
  endpoint_upper := fun j => ((repair12466Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12466Cells j).2.2

theorem repair12467Cells (j : Fin 43) :
    0 ≤ (scalarRow12467.table (sourceIndex j)).upper ∧
    (scalarRow12467.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12467.table (sourceIndex j)).centre) /
      (scalarRow12467.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12467.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12467,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12467,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12467,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12467,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12467,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12467,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12467,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12467,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12467,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12467,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12467,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12467,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12467,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12467,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12467,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12467,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12467,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12467,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12467,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12467,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12467,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12467,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12467,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12467,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12467,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12467,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12467,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12467,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12467,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12467,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12467,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12467,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12467,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12467,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12467,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12467,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12467,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12467,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12467,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12467,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12467,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12467,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12467,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12467,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12467,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12467,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12467,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12467,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12467,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12467,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12467,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12467,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12467,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12467,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12467,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12467,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12467,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12467,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12467,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12467,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12467,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12467,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12467,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12467,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12467,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12467,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12467,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12467,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12467,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12467,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12467,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12467,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12467,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12467,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12467,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12467,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12467,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12467,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12467,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12467,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12467,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12467,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12467,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12467,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12467,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12467,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12467 : FrameRepair 12467 scalarRow12467 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12467Cells j).1 (repair12467Cells j).2.1
  endpoint_upper := fun j => ((repair12467Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12467Cells j).2.2

theorem repair12468Cells (j : Fin 43) :
    0 ≤ (scalarRow12468.table (sourceIndex j)).upper ∧
    (scalarRow12468.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12468.table (sourceIndex j)).centre) /
      (scalarRow12468.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12468.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12468,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12468,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12468,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12468,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12468,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12468,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12468,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12468,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12468,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12468,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12468,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12468,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12468,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12468,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12468,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12468,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12468,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12468,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12468,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12468,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12468,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12468,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12468,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12468,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12468,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12468,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12468,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12468,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12468,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12468,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12468,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12468,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12468,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12468,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12468,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12468,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12468,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12468,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12468,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12468,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12468,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12468,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12468,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12468,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12468,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12468,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12468,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12468,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12468,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12468,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12468,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12468,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12468,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12468,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12468,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12468,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12468,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12468,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12468,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12468,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12468,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12468,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12468,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12468,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12468,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12468,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12468,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12468,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12468,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12468,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12468,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12468,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12468,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12468,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12468,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12468,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12468,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12468,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12468,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12468,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12468,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12468,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12468,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12468,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12468,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12468,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12468 : FrameRepair 12468 scalarRow12468 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12468Cells j).1 (repair12468Cells j).2.1
  endpoint_upper := fun j => ((repair12468Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12468Cells j).2.2

theorem repair12469Cells (j : Fin 43) :
    0 ≤ (scalarRow12469.table (sourceIndex j)).upper ∧
    (scalarRow12469.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12469.table (sourceIndex j)).centre) /
      (scalarRow12469.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12469.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12469,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12469,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12469,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12469,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12469,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12469,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12469,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12469,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12469,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12469,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12469,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12469,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12469,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12469,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12469,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12469,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12469,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12469,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12469,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12469,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12469,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12469,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12469,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12469,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12469,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12469,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12469,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12469,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12469,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12469,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12469,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12469,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12469,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12469,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12469,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12469,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12469,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12469,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12469,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12469,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12469,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12469,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12469,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12469,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12469,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12469,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12469,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12469,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12469,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12469,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12469,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12469,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12469,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12469,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12469,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12469,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12469,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12469,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12469,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12469,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12469,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12469,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12469,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12469,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12469,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12469,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12469,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12469,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12469,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12469,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12469,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12469,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12469,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12469,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12469,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12469,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12469,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12469,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12469,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12469,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12469,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12469,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12469,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12469,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12469,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12469,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12469 : FrameRepair 12469 scalarRow12469 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12469Cells j).1 (repair12469Cells j).2.1
  endpoint_upper := fun j => ((repair12469Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12469Cells j).2.2

theorem repair12470Cells (j : Fin 43) :
    0 ≤ (scalarRow12470.table (sourceIndex j)).upper ∧
    (scalarRow12470.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12470.table (sourceIndex j)).centre) /
      (scalarRow12470.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12470.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12470,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12470,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12470,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12470,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12470,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12470,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12470,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12470,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12470,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12470,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12470,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12470,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12470,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12470,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12470,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12470,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12470,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12470,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12470,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12470,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12470,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12470,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12470,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12470,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12470,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12470,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12470,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12470,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12470,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12470,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12470,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12470,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12470,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12470,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12470,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12470,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12470,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12470,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12470,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12470,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12470,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12470,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12470,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12470,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12470,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12470,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12470,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12470,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12470,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12470,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12470,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12470,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12470,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12470,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12470,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12470,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12470,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12470,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12470,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12470,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12470,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12470,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12470,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12470,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12470,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12470,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12470,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12470,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12470,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12470,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12470,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12470,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12470,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12470,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12470,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12470,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12470,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12470,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12470,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12470,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12470,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12470,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12470,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12470,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12470,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12470,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12470 : FrameRepair 12470 scalarRow12470 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12470Cells j).1 (repair12470Cells j).2.1
  endpoint_upper := fun j => ((repair12470Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12470Cells j).2.2

theorem repair12471Cells (j : Fin 43) :
    0 ≤ (scalarRow12471.table (sourceIndex j)).upper ∧
    (scalarRow12471.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12471.table (sourceIndex j)).centre) /
      (scalarRow12471.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12471.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12471,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12471,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12471,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12471,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12471,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12471,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12471,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12471,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12471,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12471,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12471,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12471,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12471,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12471,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12471,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12471,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12471,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12471,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12471,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12471,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12471,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12471,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12471,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12471,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12471,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12471,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12471,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12471,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12471,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12471,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12471,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12471,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12471,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12471,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12471,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12471,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12471,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12471,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12471,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12471,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12471,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12471,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12471,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12471,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12471,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12471,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12471,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12471,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12471,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12471,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12471,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12471,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12471,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12471,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12471,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12471,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12471,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12471,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12471,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12471,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12471,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12471,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12471,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12471,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12471,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12471,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12471,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12471,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12471,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12471,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12471,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12471,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12471,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12471,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12471,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12471,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12471,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12471,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12471,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12471,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12471,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12471,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12471,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12471,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12471,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12471,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12471 : FrameRepair 12471 scalarRow12471 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12471Cells j).1 (repair12471Cells j).2.1
  endpoint_upper := fun j => ((repair12471Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12471Cells j).2.2

theorem repair12472Cells (j : Fin 43) :
    0 ≤ (scalarRow12472.table (sourceIndex j)).upper ∧
    (scalarRow12472.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12472.table (sourceIndex j)).centre) /
      (scalarRow12472.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12472.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12472,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12472,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12472,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12472,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12472,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12472,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12472,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12472,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12472,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12472,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12472,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12472,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12472,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12472,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12472,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12472,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12472,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12472,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12472,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12472,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12472,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12472,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12472,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12472,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12472,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12472,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12472,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12472,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12472,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12472,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12472,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12472,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12472,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12472,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12472,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12472,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12472,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12472,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12472,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12472,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12472,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12472,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12472,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12472,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12472,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12472,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12472,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12472,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12472,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12472,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12472,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12472,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12472,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12472,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12472,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12472,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12472,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12472,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12472,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12472,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12472,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12472,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12472,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12472,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12472,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12472,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12472,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12472,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12472,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12472,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12472,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12472,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12472,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12472,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12472,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12472,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12472,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12472,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12472,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12472,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12472,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12472,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12472,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12472,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12472,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12472,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12472 : FrameRepair 12472 scalarRow12472 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12472Cells j).1 (repair12472Cells j).2.1
  endpoint_upper := fun j => ((repair12472Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12472Cells j).2.2

theorem repair12473Cells (j : Fin 43) :
    0 ≤ (scalarRow12473.table (sourceIndex j)).upper ∧
    (scalarRow12473.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12473.table (sourceIndex j)).centre) /
      (scalarRow12473.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12473.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12473,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12473,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12473,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12473,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12473,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12473,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12473,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12473,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12473,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12473,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12473,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12473,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12473,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12473,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12473,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12473,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12473,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12473,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12473,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12473,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12473,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12473,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12473,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12473,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12473,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12473,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12473,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12473,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12473,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12473,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12473,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12473,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12473,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12473,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12473,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12473,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12473,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12473,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12473,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12473,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12473,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12473,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12473,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12473,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12473,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12473,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12473,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12473,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12473,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12473,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12473,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12473,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12473,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12473,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12473,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12473,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12473,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12473,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12473,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12473,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12473,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12473,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12473,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12473,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12473,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12473,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12473,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12473,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12473,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12473,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12473,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12473,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12473,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12473,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12473,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12473,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12473,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12473,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12473,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12473,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12473,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12473,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12473,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12473,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12473,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12473,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12473 : FrameRepair 12473 scalarRow12473 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12473Cells j).1 (repair12473Cells j).2.1
  endpoint_upper := fun j => ((repair12473Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12473Cells j).2.2

theorem repair12474Cells (j : Fin 43) :
    0 ≤ (scalarRow12474.table (sourceIndex j)).upper ∧
    (scalarRow12474.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12474.table (sourceIndex j)).centre) /
      (scalarRow12474.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12474.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12474,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12474,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12474,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12474,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12474,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12474,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12474,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12474,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12474,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12474,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12474,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12474,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12474,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12474,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12474,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12474,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12474,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12474,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12474,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12474,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12474,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12474,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12474,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12474,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12474,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12474,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12474,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12474,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12474,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12474,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12474,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12474,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12474,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12474,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12474,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12474,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12474,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12474,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12474,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12474,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12474,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12474,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12474,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12474,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12474,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12474,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12474,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12474,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12474,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12474,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12474,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12474,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12474,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12474,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12474,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12474,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12474,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12474,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12474,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12474,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12474,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12474,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12474,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12474,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12474,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12474,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12474,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12474,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12474,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12474,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12474,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12474,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12474,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12474,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12474,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12474,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12474,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12474,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12474,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12474,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12474,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12474,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12474,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12474,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12474,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12474,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12474 : FrameRepair 12474 scalarRow12474 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12474Cells j).1 (repair12474Cells j).2.1
  endpoint_upper := fun j => ((repair12474Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12474Cells j).2.2

end BstLean.Part269
