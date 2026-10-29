import BstLean.Part269Rows10
import BstLean.Part269RepairCommon
namespace BstLean.Part269
open Real Set BstLean.Part255 BstLean.Part263 BstLean.Part264
theorem repair12600Cells (j : Fin 43) :
    0 ≤ (scalarRow12600.table (sourceIndex j)).upper ∧
    (scalarRow12600.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12600.table (sourceIndex j)).centre) /
      (scalarRow12600.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12600.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12600,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12600,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12600,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12600,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12600,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12600,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12600,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12600,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12600,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12600,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12600,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12600,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12600,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12600,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12600,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12600,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12600,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12600,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12600,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12600,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12600,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12600,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12600,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12600,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12600,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12600,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12600,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12600,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12600,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12600,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12600,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12600,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12600,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12600,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12600,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12600,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12600,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12600,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12600,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12600,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12600,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12600,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12600,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12600,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12600,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12600,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12600,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12600,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12600,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12600,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12600,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12600,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12600,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12600,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12600,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12600,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12600,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12600,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12600,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12600,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12600,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12600,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12600,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12600,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12600,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12600,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12600,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12600,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12600,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12600,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12600,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12600,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12600,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12600,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12600,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12600,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12600,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12600,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12600,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12600,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12600,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12600,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12600,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12600,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12600,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12600,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12600 : FrameRepair 12600 scalarRow12600 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12600Cells j).1 (repair12600Cells j).2.1
  endpoint_upper := fun j => ((repair12600Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12600Cells j).2.2

theorem repair12601Cells (j : Fin 43) :
    0 ≤ (scalarRow12601.table (sourceIndex j)).upper ∧
    (scalarRow12601.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12601.table (sourceIndex j)).centre) /
      (scalarRow12601.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12601.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12601,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12601,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12601,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12601,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12601,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12601,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12601,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12601,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12601,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12601,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12601,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12601,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12601,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12601,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12601,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12601,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12601,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12601,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12601,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12601,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12601,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12601,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12601,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12601,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12601,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12601,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12601,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12601,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12601,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12601,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12601,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12601,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12601,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12601,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12601,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12601,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12601,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12601,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12601,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12601,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12601,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12601,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12601,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12601,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12601,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12601,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12601,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12601,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12601,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12601,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12601,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12601,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12601,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12601,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12601,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12601,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12601,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12601,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12601,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12601,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12601,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12601,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12601,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12601,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12601,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12601,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12601,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12601,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12601,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12601,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12601,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12601,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12601,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12601,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12601,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12601,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12601,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12601,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12601,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12601,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12601,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12601,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12601,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12601,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12601,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12601,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12601 : FrameRepair 12601 scalarRow12601 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12601Cells j).1 (repair12601Cells j).2.1
  endpoint_upper := fun j => ((repair12601Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12601Cells j).2.2

theorem repair12602Cells (j : Fin 43) :
    0 ≤ (scalarRow12602.table (sourceIndex j)).upper ∧
    (scalarRow12602.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12602.table (sourceIndex j)).centre) /
      (scalarRow12602.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12602.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12602,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12602,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12602,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12602,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12602,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12602,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12602,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12602,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12602,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12602,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12602,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12602,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12602,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12602,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12602,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12602,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12602,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12602,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12602,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12602,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12602,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12602,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12602,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12602,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12602,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12602,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12602,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12602,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12602,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12602,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12602,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12602,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12602,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12602,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12602,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12602,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12602,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12602,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12602,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12602,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12602,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12602,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12602,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12602,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12602,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12602,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12602,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12602,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12602,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12602,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12602,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12602,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12602,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12602,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12602,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12602,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12602,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12602,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12602,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12602,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12602,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12602,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12602,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12602,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12602,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12602,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12602,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12602,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12602,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12602,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12602,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12602,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12602,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12602,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12602,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12602,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12602,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12602,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12602,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12602,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12602,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12602,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12602,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12602,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12602,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12602,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12602 : FrameRepair 12602 scalarRow12602 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12602Cells j).1 (repair12602Cells j).2.1
  endpoint_upper := fun j => ((repair12602Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12602Cells j).2.2

theorem repair12603Cells (j : Fin 43) :
    0 ≤ (scalarRow12603.table (sourceIndex j)).upper ∧
    (scalarRow12603.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12603.table (sourceIndex j)).centre) /
      (scalarRow12603.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12603.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12603,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12603,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12603,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12603,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12603,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12603,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12603,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12603,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12603,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12603,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12603,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12603,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12603,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12603,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12603,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12603,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12603,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12603,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12603,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12603,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12603,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12603,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12603,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12603,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12603,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12603,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12603,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12603,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12603,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12603,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12603,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12603,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12603,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12603,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12603,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12603,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12603,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12603,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12603,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12603,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12603,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12603,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12603,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12603,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12603,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12603,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12603,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12603,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12603,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12603,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12603,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12603,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12603,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12603,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12603,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12603,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12603,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12603,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12603,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12603,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12603,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12603,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12603,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12603,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12603,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12603,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12603,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12603,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12603,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12603,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12603,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12603,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12603,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12603,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12603,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12603,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12603,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12603,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12603,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12603,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12603,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12603,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12603,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12603,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12603,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12603,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12603 : FrameRepair 12603 scalarRow12603 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12603Cells j).1 (repair12603Cells j).2.1
  endpoint_upper := fun j => ((repair12603Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12603Cells j).2.2

theorem repair12604Cells (j : Fin 43) :
    0 ≤ (scalarRow12604.table (sourceIndex j)).upper ∧
    (scalarRow12604.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12604.table (sourceIndex j)).centre) /
      (scalarRow12604.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12604.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12604,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12604,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12604,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12604,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12604,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12604,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12604,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12604,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12604,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12604,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12604,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12604,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12604,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12604,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12604,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12604,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12604,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12604,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12604,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12604,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12604,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12604,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12604,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12604,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12604,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12604,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12604,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12604,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12604,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12604,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12604,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12604,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12604,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12604,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12604,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12604,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12604,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12604,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12604,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12604,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12604,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12604,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12604,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12604,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12604,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12604,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12604,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12604,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12604,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12604,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12604,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12604,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12604,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12604,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12604,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12604,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12604,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12604,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12604,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12604,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12604,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12604,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12604,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12604,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12604,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12604,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12604,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12604,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12604,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12604,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12604,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12604,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12604,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12604,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12604,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12604,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12604,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12604,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12604,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12604,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12604,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12604,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12604,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12604,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12604,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12604,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12604 : FrameRepair 12604 scalarRow12604 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12604Cells j).1 (repair12604Cells j).2.1
  endpoint_upper := fun j => ((repair12604Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12604Cells j).2.2

theorem repair12605Cells (j : Fin 43) :
    0 ≤ (scalarRow12605.table (sourceIndex j)).upper ∧
    (scalarRow12605.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12605.table (sourceIndex j)).centre) /
      (scalarRow12605.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12605.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12605,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12605,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12605,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12605,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12605,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12605,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12605,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12605,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12605,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12605,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12605,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12605,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12605,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12605,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12605,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12605,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12605,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12605,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12605,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12605,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12605,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12605,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12605,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12605,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12605,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12605,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12605,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12605,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12605,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12605,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12605,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12605,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12605,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12605,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12605,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12605,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12605,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12605,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12605,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12605,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12605,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12605,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12605,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12605,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12605,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12605,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12605,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12605,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12605,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12605,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12605,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12605,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12605,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12605,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12605,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12605,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12605,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12605,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12605,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12605,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12605,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12605,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12605,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12605,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12605,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12605,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12605,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12605,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12605,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12605,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12605,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12605,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12605,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12605,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12605,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12605,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12605,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12605,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12605,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12605,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12605,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12605,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12605,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12605,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12605,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12605,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12605 : FrameRepair 12605 scalarRow12605 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12605Cells j).1 (repair12605Cells j).2.1
  endpoint_upper := fun j => ((repair12605Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12605Cells j).2.2

theorem repair12606Cells (j : Fin 43) :
    0 ≤ (scalarRow12606.table (sourceIndex j)).upper ∧
    (scalarRow12606.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12606.table (sourceIndex j)).centre) /
      (scalarRow12606.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12606.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12606,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12606,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12606,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12606,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12606,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12606,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12606,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12606,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12606,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12606,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12606,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12606,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12606,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12606,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12606,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12606,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12606,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12606,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12606,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12606,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12606,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12606,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12606,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12606,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12606,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12606,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12606,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12606,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12606,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12606,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12606,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12606,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12606,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12606,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12606,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12606,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12606,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12606,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12606,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12606,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12606,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12606,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12606,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12606,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12606,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12606,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12606,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12606,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12606,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12606,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12606,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12606,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12606,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12606,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12606,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12606,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12606,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12606,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12606,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12606,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12606,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12606,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12606,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12606,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12606,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12606,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12606,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12606,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12606,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12606,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12606,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12606,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12606,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12606,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12606,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12606,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12606,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12606,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12606,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12606,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12606,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12606,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12606,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12606,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12606,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12606,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12606 : FrameRepair 12606 scalarRow12606 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12606Cells j).1 (repair12606Cells j).2.1
  endpoint_upper := fun j => ((repair12606Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12606Cells j).2.2

theorem repair12607Cells (j : Fin 43) :
    0 ≤ (scalarRow12607.table (sourceIndex j)).upper ∧
    (scalarRow12607.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12607.table (sourceIndex j)).centre) /
      (scalarRow12607.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12607.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12607,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12607,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12607,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12607,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12607,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12607,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12607,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12607,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12607,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12607,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12607,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12607,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12607,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12607,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12607,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12607,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12607,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12607,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12607,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12607,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12607,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12607,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12607,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12607,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12607,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12607,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12607,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12607,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12607,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12607,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12607,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12607,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12607,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12607,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12607,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12607,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12607,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12607,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12607,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12607,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12607,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12607,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12607,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12607,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12607,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12607,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12607,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12607,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12607,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12607,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12607,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12607,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12607,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12607,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12607,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12607,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12607,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12607,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12607,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12607,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12607,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12607,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12607,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12607,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12607,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12607,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12607,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12607,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12607,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12607,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12607,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12607,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12607,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12607,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12607,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12607,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12607,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12607,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12607,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12607,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12607,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12607,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12607,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12607,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12607,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12607,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12607 : FrameRepair 12607 scalarRow12607 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12607Cells j).1 (repair12607Cells j).2.1
  endpoint_upper := fun j => ((repair12607Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12607Cells j).2.2

theorem repair12608Cells (j : Fin 43) :
    0 ≤ (scalarRow12608.table (sourceIndex j)).upper ∧
    (scalarRow12608.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12608.table (sourceIndex j)).centre) /
      (scalarRow12608.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12608.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12608,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12608,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12608,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12608,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12608,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12608,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12608,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12608,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12608,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12608,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12608,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12608,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12608,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12608,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12608,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12608,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12608,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12608,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12608,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12608,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12608,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12608,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12608,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12608,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12608,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12608,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12608,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12608,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12608,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12608,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12608,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12608,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12608,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12608,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12608,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12608,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12608,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12608,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12608,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12608,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12608,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12608,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12608,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12608,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12608,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12608,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12608,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12608,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12608,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12608,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12608,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12608,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12608,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12608,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12608,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12608,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12608,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12608,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12608,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12608,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12608,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12608,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12608,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12608,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12608,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12608,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12608,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12608,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12608,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12608,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12608,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12608,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12608,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12608,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12608,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12608,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12608,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12608,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12608,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12608,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12608,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12608,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12608,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12608,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12608,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12608,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12608 : FrameRepair 12608 scalarRow12608 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12608Cells j).1 (repair12608Cells j).2.1
  endpoint_upper := fun j => ((repair12608Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12608Cells j).2.2

theorem repair12609Cells (j : Fin 43) :
    0 ≤ (scalarRow12609.table (sourceIndex j)).upper ∧
    (scalarRow12609.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12609.table (sourceIndex j)).centre) /
      (scalarRow12609.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12609.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12609,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12609,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12609,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12609,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12609,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12609,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12609,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12609,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12609,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12609,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12609,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12609,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12609,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12609,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12609,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12609,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12609,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12609,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12609,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12609,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12609,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12609,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12609,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12609,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12609,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12609,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12609,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12609,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12609,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12609,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12609,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12609,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12609,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12609,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12609,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12609,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12609,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12609,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12609,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12609,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12609,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12609,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12609,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12609,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12609,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12609,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12609,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12609,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12609,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12609,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12609,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12609,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12609,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12609,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12609,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12609,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12609,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12609,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12609,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12609,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12609,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12609,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12609,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12609,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12609,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12609,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12609,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12609,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12609,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12609,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12609,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12609,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12609,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12609,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12609,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12609,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12609,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12609,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12609,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12609,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12609,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12609,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12609,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12609,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12609,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12609,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12609 : FrameRepair 12609 scalarRow12609 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12609Cells j).1 (repair12609Cells j).2.1
  endpoint_upper := fun j => ((repair12609Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12609Cells j).2.2

theorem repair12610Cells (j : Fin 43) :
    0 ≤ (scalarRow12610.table (sourceIndex j)).upper ∧
    (scalarRow12610.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12610.table (sourceIndex j)).centre) /
      (scalarRow12610.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12610.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12610,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12610,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12610,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12610,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12610,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12610,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12610,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12610,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12610,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12610,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12610,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12610,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12610,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12610,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12610,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12610,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12610,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12610,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12610,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12610,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12610,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12610,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12610,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12610,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12610,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12610,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12610,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12610,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12610,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12610,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12610,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12610,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12610,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12610,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12610,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12610,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12610,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12610,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12610,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12610,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12610,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12610,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12610,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12610,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12610,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12610,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12610,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12610,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12610,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12610,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12610,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12610,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12610,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12610,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12610,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12610,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12610,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12610,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12610,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12610,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12610,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12610,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12610,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12610,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12610,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12610,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12610,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12610,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12610,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12610,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12610,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12610,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12610,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12610,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12610,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12610,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12610,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12610,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12610,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12610,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12610,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12610,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12610,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12610,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12610,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12610,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12610 : FrameRepair 12610 scalarRow12610 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12610Cells j).1 (repair12610Cells j).2.1
  endpoint_upper := fun j => ((repair12610Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12610Cells j).2.2

theorem repair12611Cells (j : Fin 43) :
    0 ≤ (scalarRow12611.table (sourceIndex j)).upper ∧
    (scalarRow12611.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12611.table (sourceIndex j)).centre) /
      (scalarRow12611.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12611.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12611,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12611,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12611,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12611,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12611,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12611,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12611,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12611,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12611,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12611,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12611,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12611,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12611,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12611,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12611,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12611,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12611,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12611,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12611,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12611,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12611,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12611,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12611,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12611,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12611,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12611,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12611,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12611,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12611,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12611,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12611,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12611,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12611,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12611,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12611,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12611,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12611,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12611,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12611,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12611,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12611,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12611,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12611,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12611,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12611,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12611,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12611,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12611,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12611,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12611,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12611,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12611,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12611,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12611,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12611,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12611,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12611,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12611,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12611,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12611,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12611,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12611,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12611,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12611,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12611,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12611,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12611,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12611,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12611,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12611,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12611,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12611,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12611,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12611,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12611,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12611,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12611,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12611,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12611,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12611,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12611,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12611,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12611,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12611,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12611,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12611,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12611 : FrameRepair 12611 scalarRow12611 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12611Cells j).1 (repair12611Cells j).2.1
  endpoint_upper := fun j => ((repair12611Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12611Cells j).2.2

theorem repair12612Cells (j : Fin 43) :
    0 ≤ (scalarRow12612.table (sourceIndex j)).upper ∧
    (scalarRow12612.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12612.table (sourceIndex j)).centre) /
      (scalarRow12612.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12612.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12612,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12612,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12612,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12612,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12612,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12612,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12612,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12612,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12612,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12612,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12612,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12612,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12612,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12612,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12612,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12612,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12612,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12612,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12612,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12612,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12612,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12612,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12612,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12612,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12612,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12612,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12612,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12612,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12612,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12612,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12612,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12612,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12612,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12612,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12612,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12612,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12612,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12612,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12612,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12612,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12612,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12612,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12612,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12612,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12612,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12612,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12612,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12612,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12612,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12612,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12612,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12612,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12612,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12612,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12612,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12612,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12612,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12612,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12612,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12612,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12612,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12612,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12612,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12612,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12612,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12612,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12612,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12612,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12612,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12612,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12612,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12612,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12612,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12612,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12612,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12612,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12612,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12612,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12612,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12612,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12612,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12612,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12612,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12612,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12612,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12612,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12612 : FrameRepair 12612 scalarRow12612 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12612Cells j).1 (repair12612Cells j).2.1
  endpoint_upper := fun j => ((repair12612Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12612Cells j).2.2

theorem repair12613Cells (j : Fin 43) :
    0 ≤ (scalarRow12613.table (sourceIndex j)).upper ∧
    (scalarRow12613.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12613.table (sourceIndex j)).centre) /
      (scalarRow12613.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12613.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12613,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12613,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12613,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12613,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12613,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12613,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12613,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12613,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12613,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12613,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12613,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12613,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12613,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12613,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12613,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12613,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12613,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12613,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12613,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12613,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12613,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12613,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12613,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12613,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12613,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12613,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12613,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12613,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12613,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12613,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12613,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12613,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12613,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12613,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12613,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12613,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12613,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12613,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12613,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12613,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12613,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12613,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12613,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12613,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12613,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12613,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12613,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12613,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12613,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12613,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12613,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12613,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12613,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12613,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12613,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12613,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12613,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12613,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12613,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12613,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12613,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12613,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12613,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12613,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12613,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12613,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12613,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12613,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12613,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12613,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12613,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12613,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12613,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12613,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12613,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12613,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12613,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12613,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12613,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12613,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12613,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12613,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12613,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12613,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12613,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12613,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12613 : FrameRepair 12613 scalarRow12613 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12613Cells j).1 (repair12613Cells j).2.1
  endpoint_upper := fun j => ((repair12613Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12613Cells j).2.2

theorem repair12614Cells (j : Fin 43) :
    0 ≤ (scalarRow12614.table (sourceIndex j)).upper ∧
    (scalarRow12614.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12614.table (sourceIndex j)).centre) /
      (scalarRow12614.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12614.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12614,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12614,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12614,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12614,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12614,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12614,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12614,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12614,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12614,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12614,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12614,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12614,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12614,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12614,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12614,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12614,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12614,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12614,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12614,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12614,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12614,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12614,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12614,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12614,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12614,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12614,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12614,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12614,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12614,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12614,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12614,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12614,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12614,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12614,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12614,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12614,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12614,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12614,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12614,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12614,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12614,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12614,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12614,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12614,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12614,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12614,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12614,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12614,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12614,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12614,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12614,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12614,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12614,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12614,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12614,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12614,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12614,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12614,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12614,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12614,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12614,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12614,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12614,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12614,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12614,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12614,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12614,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12614,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12614,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12614,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12614,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12614,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12614,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12614,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12614,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12614,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12614,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12614,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12614,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12614,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12614,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12614,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12614,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12614,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12614,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12614,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12614 : FrameRepair 12614 scalarRow12614 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12614Cells j).1 (repair12614Cells j).2.1
  endpoint_upper := fun j => ((repair12614Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12614Cells j).2.2

theorem repair12615Cells (j : Fin 43) :
    0 ≤ (scalarRow12615.table (sourceIndex j)).upper ∧
    (scalarRow12615.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12615.table (sourceIndex j)).centre) /
      (scalarRow12615.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12615.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12615,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12615,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12615,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12615,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12615,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12615,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12615,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12615,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12615,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12615,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12615,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12615,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12615,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12615,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12615,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12615,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12615,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12615,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12615,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12615,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12615,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12615,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12615,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12615,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12615,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12615,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12615,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12615,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12615,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12615,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12615,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12615,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12615,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12615,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12615,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12615,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12615,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12615,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12615,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12615,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12615,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12615,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12615,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12615,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12615,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12615,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12615,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12615,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12615,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12615,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12615,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12615,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12615,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12615,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12615,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12615,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12615,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12615,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12615,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12615,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12615,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12615,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12615,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12615,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12615,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12615,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12615,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12615,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12615,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12615,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12615,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12615,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12615,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12615,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12615,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12615,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12615,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12615,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12615,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12615,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12615,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12615,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12615,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12615,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12615,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12615,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12615 : FrameRepair 12615 scalarRow12615 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12615Cells j).1 (repair12615Cells j).2.1
  endpoint_upper := fun j => ((repair12615Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12615Cells j).2.2

theorem repair12616Cells (j : Fin 43) :
    0 ≤ (scalarRow12616.table (sourceIndex j)).upper ∧
    (scalarRow12616.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12616.table (sourceIndex j)).centre) /
      (scalarRow12616.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12616.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12616,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12616,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12616,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12616,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12616,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12616,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12616,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12616,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12616,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12616,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12616,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12616,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12616,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12616,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12616,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12616,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12616,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12616,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12616,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12616,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12616,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12616,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12616,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12616,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12616,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12616,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12616,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12616,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12616,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12616,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12616,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12616,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12616,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12616,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12616,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12616,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12616,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12616,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12616,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12616,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12616,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12616,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12616,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12616,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12616,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12616,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12616,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12616,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12616,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12616,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12616,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12616,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12616,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12616,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12616,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12616,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12616,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12616,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12616,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12616,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12616,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12616,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12616,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12616,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12616,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12616,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12616,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12616,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12616,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12616,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12616,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12616,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12616,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12616,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12616,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12616,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12616,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12616,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12616,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12616,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12616,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12616,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12616,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12616,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12616,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12616,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12616 : FrameRepair 12616 scalarRow12616 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12616Cells j).1 (repair12616Cells j).2.1
  endpoint_upper := fun j => ((repair12616Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12616Cells j).2.2

theorem repair12617Cells (j : Fin 43) :
    0 ≤ (scalarRow12617.table (sourceIndex j)).upper ∧
    (scalarRow12617.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12617.table (sourceIndex j)).centre) /
      (scalarRow12617.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12617.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12617,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12617,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12617,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12617,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12617,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12617,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12617,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12617,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12617,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12617,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12617,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12617,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12617,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12617,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12617,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12617,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12617,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12617,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12617,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12617,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12617,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12617,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12617,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12617,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12617,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12617,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12617,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12617,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12617,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12617,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12617,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12617,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12617,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12617,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12617,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12617,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12617,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12617,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12617,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12617,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12617,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12617,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12617,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12617,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12617,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12617,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12617,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12617,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12617,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12617,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12617,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12617,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12617,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12617,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12617,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12617,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12617,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12617,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12617,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12617,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12617,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12617,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12617,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12617,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12617,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12617,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12617,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12617,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12617,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12617,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12617,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12617,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12617,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12617,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12617,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12617,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12617,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12617,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12617,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12617,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12617,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12617,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12617,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12617,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12617,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12617,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12617 : FrameRepair 12617 scalarRow12617 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12617Cells j).1 (repair12617Cells j).2.1
  endpoint_upper := fun j => ((repair12617Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12617Cells j).2.2

theorem repair12618Cells (j : Fin 43) :
    0 ≤ (scalarRow12618.table (sourceIndex j)).upper ∧
    (scalarRow12618.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12618.table (sourceIndex j)).centre) /
      (scalarRow12618.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12618.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12618,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12618,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12618,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12618,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12618,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12618,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12618,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12618,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12618,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12618,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12618,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12618,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12618,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12618,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12618,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12618,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12618,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12618,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12618,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12618,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12618,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12618,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12618,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12618,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12618,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12618,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12618,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12618,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12618,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12618,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12618,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12618,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12618,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12618,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12618,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12618,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12618,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12618,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12618,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12618,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12618,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12618,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12618,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12618,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12618,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12618,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12618,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12618,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12618,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12618,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12618,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12618,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12618,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12618,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12618,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12618,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12618,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12618,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12618,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12618,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12618,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12618,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12618,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12618,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12618,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12618,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12618,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12618,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12618,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12618,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12618,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12618,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12618,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12618,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12618,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12618,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12618,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12618,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12618,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12618,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12618,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12618,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12618,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12618,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12618,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12618,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12618 : FrameRepair 12618 scalarRow12618 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12618Cells j).1 (repair12618Cells j).2.1
  endpoint_upper := fun j => ((repair12618Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12618Cells j).2.2

theorem repair12619Cells (j : Fin 43) :
    0 ≤ (scalarRow12619.table (sourceIndex j)).upper ∧
    (scalarRow12619.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12619.table (sourceIndex j)).centre) /
      (scalarRow12619.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12619.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12619,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12619,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12619,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12619,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12619,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12619,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12619,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12619,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12619,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12619,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12619,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12619,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12619,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12619,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12619,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12619,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12619,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12619,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12619,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12619,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12619,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12619,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12619,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12619,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12619,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12619,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12619,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12619,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12619,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12619,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12619,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12619,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12619,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12619,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12619,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12619,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12619,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12619,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12619,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12619,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12619,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12619,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12619,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12619,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12619,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12619,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12619,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12619,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12619,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12619,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12619,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12619,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12619,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12619,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12619,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12619,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12619,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12619,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12619,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12619,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12619,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12619,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12619,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12619,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12619,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12619,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12619,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12619,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12619,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12619,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12619,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12619,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12619,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12619,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12619,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12619,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12619,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12619,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12619,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12619,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12619,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12619,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12619,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12619,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12619,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12619,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12619 : FrameRepair 12619 scalarRow12619 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12619Cells j).1 (repair12619Cells j).2.1
  endpoint_upper := fun j => ((repair12619Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12619Cells j).2.2

theorem repair12620Cells (j : Fin 43) :
    0 ≤ (scalarRow12620.table (sourceIndex j)).upper ∧
    (scalarRow12620.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12620.table (sourceIndex j)).centre) /
      (scalarRow12620.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12620.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12620,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12620,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12620,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12620,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12620,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12620,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12620,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12620,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12620,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12620,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12620,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12620,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12620,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12620,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12620,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12620,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12620,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12620,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12620,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12620,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12620,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12620,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12620,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12620,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12620,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12620,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12620,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12620,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12620,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12620,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12620,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12620,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12620,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12620,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12620,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12620,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12620,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12620,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12620,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12620,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12620,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12620,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12620,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12620,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12620,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12620,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12620,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12620,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12620,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12620,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12620,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12620,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12620,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12620,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12620,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12620,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12620,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12620,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12620,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12620,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12620,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12620,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12620,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12620,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12620,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12620,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12620,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12620,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12620,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12620,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12620,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12620,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12620,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12620,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12620,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12620,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12620,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12620,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12620,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12620,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12620,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12620,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12620,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12620,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12620,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12620,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12620 : FrameRepair 12620 scalarRow12620 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12620Cells j).1 (repair12620Cells j).2.1
  endpoint_upper := fun j => ((repair12620Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12620Cells j).2.2

theorem repair12621Cells (j : Fin 43) :
    0 ≤ (scalarRow12621.table (sourceIndex j)).upper ∧
    (scalarRow12621.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12621.table (sourceIndex j)).centre) /
      (scalarRow12621.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12621.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12621,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12621,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12621,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12621,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12621,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12621,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12621,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12621,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12621,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12621,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12621,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12621,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12621,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12621,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12621,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12621,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12621,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12621,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12621,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12621,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12621,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12621,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12621,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12621,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12621,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12621,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12621,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12621,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12621,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12621,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12621,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12621,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12621,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12621,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12621,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12621,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12621,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12621,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12621,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12621,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12621,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12621,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12621,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12621,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12621,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12621,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12621,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12621,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12621,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12621,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12621,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12621,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12621,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12621,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12621,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12621,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12621,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12621,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12621,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12621,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12621,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12621,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12621,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12621,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12621,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12621,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12621,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12621,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12621,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12621,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12621,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12621,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12621,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12621,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12621,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12621,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12621,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12621,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12621,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12621,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12621,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12621,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12621,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12621,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12621,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12621,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12621 : FrameRepair 12621 scalarRow12621 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12621Cells j).1 (repair12621Cells j).2.1
  endpoint_upper := fun j => ((repair12621Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12621Cells j).2.2

theorem repair12622Cells (j : Fin 43) :
    0 ≤ (scalarRow12622.table (sourceIndex j)).upper ∧
    (scalarRow12622.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12622.table (sourceIndex j)).centre) /
      (scalarRow12622.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12622.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12622,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12622,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12622,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12622,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12622,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12622,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12622,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12622,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12622,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12622,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12622,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12622,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12622,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12622,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12622,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12622,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12622,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12622,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12622,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12622,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12622,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12622,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12622,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12622,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12622,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12622,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12622,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12622,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12622,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12622,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12622,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12622,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12622,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12622,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12622,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12622,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12622,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12622,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12622,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12622,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12622,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12622,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12622,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12622,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12622,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12622,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12622,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12622,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12622,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12622,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12622,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12622,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12622,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12622,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12622,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12622,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12622,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12622,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12622,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12622,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12622,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12622,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12622,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12622,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12622,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12622,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12622,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12622,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12622,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12622,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12622,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12622,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12622,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12622,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12622,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12622,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12622,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12622,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12622,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12622,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12622,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12622,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12622,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12622,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12622,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12622,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12622 : FrameRepair 12622 scalarRow12622 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12622Cells j).1 (repair12622Cells j).2.1
  endpoint_upper := fun j => ((repair12622Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12622Cells j).2.2

theorem repair12623Cells (j : Fin 43) :
    0 ≤ (scalarRow12623.table (sourceIndex j)).upper ∧
    (scalarRow12623.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12623.table (sourceIndex j)).centre) /
      (scalarRow12623.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12623.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12623,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12623,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12623,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12623,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12623,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12623,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12623,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12623,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12623,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12623,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12623,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12623,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12623,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12623,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12623,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12623,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12623,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12623,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12623,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12623,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12623,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12623,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12623,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12623,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12623,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12623,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12623,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12623,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12623,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12623,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12623,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12623,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12623,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12623,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12623,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12623,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12623,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12623,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12623,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12623,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12623,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12623,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12623,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12623,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12623,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12623,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12623,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12623,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12623,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12623,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12623,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12623,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12623,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12623,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12623,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12623,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12623,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12623,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12623,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12623,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12623,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12623,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12623,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12623,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12623,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12623,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12623,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12623,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12623,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12623,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12623,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12623,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12623,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12623,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12623,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12623,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12623,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12623,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12623,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12623,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12623,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12623,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12623,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12623,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12623,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12623,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12623 : FrameRepair 12623 scalarRow12623 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12623Cells j).1 (repair12623Cells j).2.1
  endpoint_upper := fun j => ((repair12623Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12623Cells j).2.2

theorem repair12624Cells (j : Fin 43) :
    0 ≤ (scalarRow12624.table (sourceIndex j)).upper ∧
    (scalarRow12624.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12624.table (sourceIndex j)).centre) /
      (scalarRow12624.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12624.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12624,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12624,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12624,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12624,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12624,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12624,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12624,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12624,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12624,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12624,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12624,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12624,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12624,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12624,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12624,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12624,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12624,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12624,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12624,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12624,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12624,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12624,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12624,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12624,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12624,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12624,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12624,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12624,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12624,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12624,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12624,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12624,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12624,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12624,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12624,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12624,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12624,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12624,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12624,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12624,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12624,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12624,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12624,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12624,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12624,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12624,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12624,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12624,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12624,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12624,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12624,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12624,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12624,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12624,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12624,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12624,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12624,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12624,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12624,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12624,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12624,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12624,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12624,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12624,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12624,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12624,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12624,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12624,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12624,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12624,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12624,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12624,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12624,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12624,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12624,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12624,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12624,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12624,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12624,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12624,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12624,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12624,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12624,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12624,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12624,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12624,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12624 : FrameRepair 12624 scalarRow12624 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12624Cells j).1 (repair12624Cells j).2.1
  endpoint_upper := fun j => ((repair12624Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12624Cells j).2.2

end BstLean.Part269
