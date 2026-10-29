import BstLean.Part269Rows26
import BstLean.Part269RepairCommon
namespace BstLean.Part269
open Real Set BstLean.Part255 BstLean.Part263 BstLean.Part264
theorem repair13000Cells (j : Fin 43) :
    0 ≤ (scalarRow13000.table (sourceIndex j)).upper ∧
    (scalarRow13000.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13000.table (sourceIndex j)).centre) /
      (scalarRow13000.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13000.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13000,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13000,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13000,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13000,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13000,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13000,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13000,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13000,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13000,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13000,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13000,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13000,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13000,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13000,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13000,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13000,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13000,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13000,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13000,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13000,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13000,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13000,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13000,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13000,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13000,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13000,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13000,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13000,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13000,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13000,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13000,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13000,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13000,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13000,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13000,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13000,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13000,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13000,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13000,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13000,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13000,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13000,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13000,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13000,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13000,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13000,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13000,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13000,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13000,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13000,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13000,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13000,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13000,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13000,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13000,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13000,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13000,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13000,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13000,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13000,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13000,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13000,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13000,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13000,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13000,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13000,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13000,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13000,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13000,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13000,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13000,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13000,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13000,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13000,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13000,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13000,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13000,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13000,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13000,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13000,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13000,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13000,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13000,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13000,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13000,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13000,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13000 : FrameRepair 13000 scalarRow13000 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13000Cells j).1 (repair13000Cells j).2.1
  endpoint_upper := fun j => ((repair13000Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13000Cells j).2.2

theorem repair13001Cells (j : Fin 43) :
    0 ≤ (scalarRow13001.table (sourceIndex j)).upper ∧
    (scalarRow13001.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13001.table (sourceIndex j)).centre) /
      (scalarRow13001.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13001.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13001,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13001,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13001,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13001,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13001,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13001,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13001,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13001,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13001,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13001,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13001,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13001,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13001,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13001,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13001,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13001,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13001,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13001,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13001,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13001,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13001,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13001,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13001,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13001,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13001,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13001,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13001,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13001,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13001,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13001,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13001,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13001,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13001,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13001,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13001,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13001,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13001,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13001,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13001,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13001,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13001,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13001,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13001,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13001,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13001,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13001,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13001,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13001,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13001,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13001,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13001,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13001,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13001,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13001,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13001,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13001,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13001,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13001,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13001,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13001,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13001,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13001,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13001,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13001,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13001,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13001,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13001,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13001,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13001,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13001,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13001,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13001,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13001,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13001,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13001,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13001,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13001,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13001,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13001,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13001,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13001,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13001,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13001,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13001,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13001,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13001,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13001 : FrameRepair 13001 scalarRow13001 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13001Cells j).1 (repair13001Cells j).2.1
  endpoint_upper := fun j => ((repair13001Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13001Cells j).2.2

theorem repair13002Cells (j : Fin 43) :
    0 ≤ (scalarRow13002.table (sourceIndex j)).upper ∧
    (scalarRow13002.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13002.table (sourceIndex j)).centre) /
      (scalarRow13002.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13002.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13002,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13002,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13002,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13002,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13002,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13002,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13002,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13002,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13002,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13002,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13002,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13002,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13002,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13002,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13002,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13002,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13002,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13002,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13002,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13002,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13002,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13002,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13002,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13002,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13002,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13002,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13002,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13002,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13002,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13002,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13002,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13002,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13002,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13002,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13002,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13002,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13002,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13002,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13002,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13002,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13002,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13002,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13002,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13002,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13002,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13002,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13002,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13002,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13002,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13002,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13002,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13002,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13002,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13002,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13002,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13002,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13002,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13002,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13002,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13002,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13002,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13002,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13002,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13002,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13002,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13002,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13002,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13002,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13002,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13002,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13002,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13002,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13002,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13002,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13002,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13002,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13002,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13002,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13002,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13002,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13002,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13002,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13002,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13002,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13002,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13002,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13002 : FrameRepair 13002 scalarRow13002 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13002Cells j).1 (repair13002Cells j).2.1
  endpoint_upper := fun j => ((repair13002Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13002Cells j).2.2

theorem repair13003Cells (j : Fin 43) :
    0 ≤ (scalarRow13003.table (sourceIndex j)).upper ∧
    (scalarRow13003.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13003.table (sourceIndex j)).centre) /
      (scalarRow13003.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13003.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13003,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13003,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13003,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13003,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13003,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13003,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13003,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13003,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13003,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13003,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13003,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13003,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13003,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13003,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13003,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13003,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13003,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13003,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13003,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13003,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13003,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13003,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13003,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13003,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13003,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13003,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13003,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13003,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13003,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13003,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13003,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13003,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13003,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13003,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13003,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13003,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13003,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13003,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13003,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13003,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13003,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13003,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13003,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13003,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13003,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13003,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13003,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13003,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13003,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13003,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13003,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13003,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13003,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13003,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13003,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13003,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13003,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13003,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13003,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13003,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13003,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13003,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13003,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13003,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13003,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13003,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13003,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13003,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13003,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13003,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13003,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13003,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13003,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13003,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13003,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13003,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13003,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13003,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13003,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13003,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13003,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13003,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13003,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13003,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13003,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13003,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13003 : FrameRepair 13003 scalarRow13003 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13003Cells j).1 (repair13003Cells j).2.1
  endpoint_upper := fun j => ((repair13003Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13003Cells j).2.2

theorem repair13004Cells (j : Fin 43) :
    0 ≤ (scalarRow13004.table (sourceIndex j)).upper ∧
    (scalarRow13004.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13004.table (sourceIndex j)).centre) /
      (scalarRow13004.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13004.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13004,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13004,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13004,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13004,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13004,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13004,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13004,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13004,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13004,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13004,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13004,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13004,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13004,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13004,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13004,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13004,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13004,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13004,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13004,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13004,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13004,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13004,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13004,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13004,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13004,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13004,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13004,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13004,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13004,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13004,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13004,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13004,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13004,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13004,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13004,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13004,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13004,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13004,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13004,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13004,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13004,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13004,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13004,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13004,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13004,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13004,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13004,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13004,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13004,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13004,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13004,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13004,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13004,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13004,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13004,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13004,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13004,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13004,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13004,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13004,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13004,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13004,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13004,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13004,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13004,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13004,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13004,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13004,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13004,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13004,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13004,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13004,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13004,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13004,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13004,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13004,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13004,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13004,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13004,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13004,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13004,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13004,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13004,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13004,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13004,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13004,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13004 : FrameRepair 13004 scalarRow13004 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13004Cells j).1 (repair13004Cells j).2.1
  endpoint_upper := fun j => ((repair13004Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13004Cells j).2.2

theorem repair13005Cells (j : Fin 43) :
    0 ≤ (scalarRow13005.table (sourceIndex j)).upper ∧
    (scalarRow13005.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13005.table (sourceIndex j)).centre) /
      (scalarRow13005.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13005.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13005,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13005,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13005,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13005,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13005,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13005,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13005,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13005,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13005,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13005,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13005,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13005,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13005,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13005,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13005,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13005,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13005,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13005,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13005,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13005,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13005,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13005,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13005,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13005,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13005,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13005,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13005,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13005,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13005,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13005,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13005,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13005,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13005,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13005,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13005,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13005,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13005,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13005,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13005,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13005,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13005,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13005,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13005,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13005,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13005,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13005,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13005,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13005,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13005,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13005,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13005,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13005,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13005,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13005,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13005,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13005,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13005,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13005,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13005,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13005,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13005,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13005,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13005,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13005,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13005,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13005,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13005,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13005,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13005,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13005,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13005,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13005,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13005,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13005,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13005,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13005,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13005,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13005,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13005,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13005,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13005,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13005,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13005,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13005,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13005,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13005,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13005 : FrameRepair 13005 scalarRow13005 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13005Cells j).1 (repair13005Cells j).2.1
  endpoint_upper := fun j => ((repair13005Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13005Cells j).2.2

theorem repair13006Cells (j : Fin 43) :
    0 ≤ (scalarRow13006.table (sourceIndex j)).upper ∧
    (scalarRow13006.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13006.table (sourceIndex j)).centre) /
      (scalarRow13006.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13006.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13006,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13006,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13006,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13006,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13006,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13006,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13006,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13006,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13006,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13006,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13006,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13006,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13006,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13006,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13006,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13006,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13006,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13006,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13006,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13006,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13006,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13006,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13006,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13006,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13006,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13006,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13006,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13006,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13006,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13006,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13006,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13006,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13006,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13006,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13006,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13006,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13006,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13006,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13006,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13006,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13006,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13006,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13006,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13006,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13006,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13006,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13006,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13006,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13006,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13006,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13006,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13006,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13006,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13006,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13006,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13006,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13006,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13006,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13006,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13006,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13006,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13006,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13006,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13006,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13006,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13006,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13006,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13006,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13006,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13006,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13006,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13006,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13006,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13006,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13006,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13006,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13006,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13006,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13006,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13006,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13006,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13006,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13006,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13006,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13006,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13006,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13006 : FrameRepair 13006 scalarRow13006 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13006Cells j).1 (repair13006Cells j).2.1
  endpoint_upper := fun j => ((repair13006Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13006Cells j).2.2

theorem repair13007Cells (j : Fin 43) :
    0 ≤ (scalarRow13007.table (sourceIndex j)).upper ∧
    (scalarRow13007.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13007.table (sourceIndex j)).centre) /
      (scalarRow13007.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13007.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13007,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13007,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13007,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13007,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13007,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13007,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13007,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13007,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13007,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13007,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13007,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13007,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13007,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13007,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13007,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13007,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13007,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13007,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13007,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13007,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13007,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13007,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13007,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13007,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13007,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13007,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13007,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13007,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13007,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13007,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13007,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13007,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13007,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13007,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13007,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13007,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13007,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13007,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13007,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13007,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13007,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13007,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13007,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13007,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13007,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13007,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13007,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13007,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13007,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13007,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13007,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13007,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13007,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13007,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13007,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13007,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13007,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13007,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13007,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13007,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13007,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13007,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13007,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13007,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13007,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13007,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13007,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13007,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13007,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13007,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13007,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13007,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13007,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13007,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13007,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13007,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13007,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13007,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13007,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13007,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13007,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13007,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13007,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13007,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13007,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13007,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13007 : FrameRepair 13007 scalarRow13007 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13007Cells j).1 (repair13007Cells j).2.1
  endpoint_upper := fun j => ((repair13007Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13007Cells j).2.2

theorem repair13008Cells (j : Fin 43) :
    0 ≤ (scalarRow13008.table (sourceIndex j)).upper ∧
    (scalarRow13008.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13008.table (sourceIndex j)).centre) /
      (scalarRow13008.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13008.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13008,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13008,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13008,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13008,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13008,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13008,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13008,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13008,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13008,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13008,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13008,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13008,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13008,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13008,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13008,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13008,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13008,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13008,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13008,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13008,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13008,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13008,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13008,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13008,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13008,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13008,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13008,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13008,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13008,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13008,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13008,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13008,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13008,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13008,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13008,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13008,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13008,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13008,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13008,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13008,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13008,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13008,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13008,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13008,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13008,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13008,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13008,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13008,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13008,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13008,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13008,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13008,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13008,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13008,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13008,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13008,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13008,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13008,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13008,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13008,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13008,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13008,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13008,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13008,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13008,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13008,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13008,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13008,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13008,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13008,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13008,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13008,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13008,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13008,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13008,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13008,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13008,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13008,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13008,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13008,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13008,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13008,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13008,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13008,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13008,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13008,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13008 : FrameRepair 13008 scalarRow13008 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13008Cells j).1 (repair13008Cells j).2.1
  endpoint_upper := fun j => ((repair13008Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13008Cells j).2.2

theorem repair13009Cells (j : Fin 43) :
    0 ≤ (scalarRow13009.table (sourceIndex j)).upper ∧
    (scalarRow13009.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13009.table (sourceIndex j)).centre) /
      (scalarRow13009.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13009.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13009,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13009,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13009,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13009,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13009,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13009,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13009,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13009,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13009,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13009,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13009,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13009,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13009,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13009,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13009,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13009,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13009,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13009,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13009,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13009,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13009,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13009,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13009,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13009,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13009,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13009,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13009,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13009,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13009,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13009,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13009,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13009,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13009,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13009,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13009,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13009,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13009,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13009,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13009,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13009,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13009,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13009,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13009,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13009,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13009,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13009,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13009,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13009,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13009,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13009,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13009,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13009,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13009,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13009,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13009,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13009,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13009,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13009,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13009,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13009,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13009,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13009,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13009,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13009,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13009,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13009,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13009,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13009,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13009,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13009,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13009,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13009,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13009,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13009,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13009,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13009,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13009,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13009,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13009,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13009,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13009,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13009,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13009,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13009,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13009,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13009,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13009 : FrameRepair 13009 scalarRow13009 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13009Cells j).1 (repair13009Cells j).2.1
  endpoint_upper := fun j => ((repair13009Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13009Cells j).2.2

theorem repair13010Cells (j : Fin 43) :
    0 ≤ (scalarRow13010.table (sourceIndex j)).upper ∧
    (scalarRow13010.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13010.table (sourceIndex j)).centre) /
      (scalarRow13010.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13010.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13010,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13010,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13010,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13010,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13010,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13010,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13010,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13010,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13010,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13010,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13010,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13010,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13010,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13010,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13010,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13010,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13010,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13010,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13010,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13010,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13010,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13010,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13010,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13010,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13010,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13010,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13010,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13010,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13010,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13010,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13010,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13010,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13010,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13010,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13010,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13010,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13010,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13010,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13010,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13010,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13010,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13010,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13010,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13010,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13010,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13010,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13010,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13010,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13010,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13010,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13010,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13010,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13010,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13010,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13010,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13010,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13010,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13010,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13010,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13010,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13010,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13010,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13010,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13010,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13010,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13010,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13010,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13010,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13010,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13010,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13010,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13010,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13010,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13010,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13010,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13010,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13010,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13010,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13010,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13010,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13010,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13010,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13010,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13010,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13010,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13010,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13010 : FrameRepair 13010 scalarRow13010 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13010Cells j).1 (repair13010Cells j).2.1
  endpoint_upper := fun j => ((repair13010Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13010Cells j).2.2

theorem repair13011Cells (j : Fin 43) :
    0 ≤ (scalarRow13011.table (sourceIndex j)).upper ∧
    (scalarRow13011.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13011.table (sourceIndex j)).centre) /
      (scalarRow13011.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13011.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13011,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13011,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13011,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13011,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13011,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13011,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13011,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13011,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13011,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13011,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13011,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13011,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13011,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13011,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13011,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13011,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13011,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13011,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13011,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13011,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13011,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13011,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13011,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13011,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13011,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13011,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13011,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13011,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13011,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13011,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13011,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13011,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13011,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13011,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13011,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13011,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13011,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13011,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13011,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13011,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13011,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13011,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13011,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13011,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13011,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13011,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13011,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13011,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13011,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13011,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13011,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13011,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13011,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13011,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13011,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13011,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13011,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13011,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13011,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13011,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13011,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13011,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13011,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13011,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13011,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13011,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13011,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13011,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13011,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13011,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13011,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13011,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13011,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13011,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13011,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13011,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13011,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13011,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13011,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13011,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13011,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13011,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13011,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13011,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13011,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13011,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13011 : FrameRepair 13011 scalarRow13011 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13011Cells j).1 (repair13011Cells j).2.1
  endpoint_upper := fun j => ((repair13011Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13011Cells j).2.2

theorem repair13012Cells (j : Fin 43) :
    0 ≤ (scalarRow13012.table (sourceIndex j)).upper ∧
    (scalarRow13012.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13012.table (sourceIndex j)).centre) /
      (scalarRow13012.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13012.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13012,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13012,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13012,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13012,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13012,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13012,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13012,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13012,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13012,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13012,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13012,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13012,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13012,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13012,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13012,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13012,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13012,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13012,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13012,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13012,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13012,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13012,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13012,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13012,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13012,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13012,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13012,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13012,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13012,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13012,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13012,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13012,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13012,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13012,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13012,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13012,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13012,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13012,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13012,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13012,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13012,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13012,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13012,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13012,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13012,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13012,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13012,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13012,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13012,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13012,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13012,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13012,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13012,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13012,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13012,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13012,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13012,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13012,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13012,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13012,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13012,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13012,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13012,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13012,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13012,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13012,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13012,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13012,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13012,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13012,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13012,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13012,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13012,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13012,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13012,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13012,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13012,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13012,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13012,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13012,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13012,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13012,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13012,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13012,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13012,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13012,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13012 : FrameRepair 13012 scalarRow13012 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13012Cells j).1 (repair13012Cells j).2.1
  endpoint_upper := fun j => ((repair13012Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13012Cells j).2.2

theorem repair13013Cells (j : Fin 43) :
    0 ≤ (scalarRow13013.table (sourceIndex j)).upper ∧
    (scalarRow13013.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13013.table (sourceIndex j)).centre) /
      (scalarRow13013.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13013.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13013,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13013,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13013,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13013,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13013,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13013,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13013,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13013,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13013,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13013,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13013,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13013,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13013,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13013,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13013,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13013,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13013,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13013,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13013,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13013,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13013,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13013,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13013,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13013,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13013,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13013,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13013,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13013,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13013,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13013,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13013,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13013,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13013,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13013,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13013,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13013,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13013,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13013,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13013,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13013,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13013,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13013,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13013,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13013,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13013,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13013,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13013,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13013,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13013,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13013,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13013,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13013,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13013,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13013,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13013,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13013,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13013,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13013,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13013,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13013,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13013,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13013,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13013,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13013,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13013,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13013,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13013,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13013,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13013,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13013,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13013,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13013,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13013,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13013,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13013,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13013,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13013,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13013,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13013,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13013,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13013,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13013,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13013,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13013,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13013,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13013,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13013 : FrameRepair 13013 scalarRow13013 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13013Cells j).1 (repair13013Cells j).2.1
  endpoint_upper := fun j => ((repair13013Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13013Cells j).2.2

theorem repair13014Cells (j : Fin 43) :
    0 ≤ (scalarRow13014.table (sourceIndex j)).upper ∧
    (scalarRow13014.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13014.table (sourceIndex j)).centre) /
      (scalarRow13014.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13014.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13014,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13014,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13014,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13014,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13014,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13014,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13014,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13014,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13014,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13014,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13014,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13014,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13014,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13014,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13014,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13014,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13014,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13014,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13014,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13014,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13014,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13014,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13014,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13014,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13014,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13014,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13014,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13014,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13014,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13014,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13014,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13014,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13014,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13014,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13014,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13014,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13014,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13014,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13014,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13014,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13014,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13014,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13014,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13014,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13014,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13014,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13014,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13014,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13014,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13014,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13014,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13014,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13014,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13014,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13014,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13014,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13014,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13014,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13014,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13014,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13014,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13014,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13014,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13014,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13014,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13014,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13014,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13014,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13014,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13014,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13014,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13014,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13014,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13014,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13014,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13014,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13014,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13014,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13014,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13014,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13014,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13014,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13014,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13014,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13014,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13014,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13014 : FrameRepair 13014 scalarRow13014 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13014Cells j).1 (repair13014Cells j).2.1
  endpoint_upper := fun j => ((repair13014Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13014Cells j).2.2

theorem repair13015Cells (j : Fin 43) :
    0 ≤ (scalarRow13015.table (sourceIndex j)).upper ∧
    (scalarRow13015.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13015.table (sourceIndex j)).centre) /
      (scalarRow13015.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13015.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13015,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13015,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13015,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13015,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13015,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13015,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13015,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13015,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13015,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13015,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13015,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13015,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13015,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13015,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13015,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13015,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13015,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13015,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13015,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13015,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13015,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13015,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13015,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13015,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13015,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13015,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13015,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13015,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13015,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13015,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13015,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13015,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13015,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13015,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13015,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13015,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13015,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13015,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13015,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13015,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13015,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13015,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13015,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13015,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13015,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13015,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13015,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13015,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13015,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13015,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13015,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13015,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13015,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13015,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13015,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13015,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13015,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13015,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13015,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13015,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13015,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13015,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13015,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13015,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13015,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13015,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13015,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13015,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13015,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13015,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13015,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13015,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13015,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13015,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13015,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13015,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13015,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13015,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13015,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13015,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13015,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13015,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13015,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13015,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13015,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13015,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13015 : FrameRepair 13015 scalarRow13015 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13015Cells j).1 (repair13015Cells j).2.1
  endpoint_upper := fun j => ((repair13015Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13015Cells j).2.2

theorem repair13016Cells (j : Fin 43) :
    0 ≤ (scalarRow13016.table (sourceIndex j)).upper ∧
    (scalarRow13016.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13016.table (sourceIndex j)).centre) /
      (scalarRow13016.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13016.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13016,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13016,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13016,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13016,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13016,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13016,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13016,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13016,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13016,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13016,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13016,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13016,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13016,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13016,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13016,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13016,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13016,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13016,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13016,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13016,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13016,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13016,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13016,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13016,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13016,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13016,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13016,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13016,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13016,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13016,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13016,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13016,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13016,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13016,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13016,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13016,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13016,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13016,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13016,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13016,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13016,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13016,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13016,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13016,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13016,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13016,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13016,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13016,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13016,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13016,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13016,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13016,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13016,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13016,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13016,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13016,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13016,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13016,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13016,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13016,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13016,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13016,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13016,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13016,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13016,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13016,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13016,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13016,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13016,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13016,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13016,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13016,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13016,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13016,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13016,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13016,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13016,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13016,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13016,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13016,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13016,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13016,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13016,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13016,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13016,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13016,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13016 : FrameRepair 13016 scalarRow13016 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13016Cells j).1 (repair13016Cells j).2.1
  endpoint_upper := fun j => ((repair13016Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13016Cells j).2.2

theorem repair13017Cells (j : Fin 43) :
    0 ≤ (scalarRow13017.table (sourceIndex j)).upper ∧
    (scalarRow13017.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13017.table (sourceIndex j)).centre) /
      (scalarRow13017.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13017.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13017,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13017,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13017,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13017,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13017,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13017,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13017,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13017,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13017,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13017,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13017,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13017,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13017,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13017,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13017,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13017,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13017,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13017,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13017,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13017,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13017,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13017,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13017,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13017,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13017,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13017,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13017,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13017,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13017,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13017,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13017,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13017,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13017,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13017,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13017,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13017,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13017,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13017,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13017,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13017,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13017,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13017,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13017,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13017,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13017,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13017,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13017,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13017,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13017,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13017,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13017,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13017,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13017,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13017,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13017,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13017,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13017,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13017,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13017,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13017,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13017,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13017,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13017,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13017,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13017,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13017,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13017,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13017,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13017,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13017,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13017,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13017,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13017,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13017,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13017,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13017,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13017,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13017,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13017,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13017,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13017,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13017,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13017,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13017,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13017,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13017,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13017 : FrameRepair 13017 scalarRow13017 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13017Cells j).1 (repair13017Cells j).2.1
  endpoint_upper := fun j => ((repair13017Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13017Cells j).2.2

theorem repair13018Cells (j : Fin 43) :
    0 ≤ (scalarRow13018.table (sourceIndex j)).upper ∧
    (scalarRow13018.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13018.table (sourceIndex j)).centre) /
      (scalarRow13018.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13018.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13018,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13018,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13018,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13018,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13018,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13018,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13018,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13018,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13018,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13018,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13018,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13018,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13018,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13018,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13018,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13018,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13018,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13018,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13018,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13018,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13018,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13018,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13018,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13018,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13018,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13018,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13018,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13018,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13018,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13018,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13018,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13018,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13018,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13018,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13018,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13018,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13018,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13018,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13018,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13018,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13018,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13018,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13018,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13018,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13018,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13018,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13018,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13018,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13018,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13018,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13018,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13018,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13018,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13018,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13018,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13018,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13018,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13018,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13018,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13018,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13018,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13018,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13018,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13018,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13018,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13018,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13018,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13018,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13018,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13018,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13018,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13018,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13018,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13018,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13018,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13018,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13018,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13018,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13018,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13018,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13018,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13018,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13018,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13018,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13018,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13018,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13018 : FrameRepair 13018 scalarRow13018 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13018Cells j).1 (repair13018Cells j).2.1
  endpoint_upper := fun j => ((repair13018Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13018Cells j).2.2

theorem repair13019Cells (j : Fin 43) :
    0 ≤ (scalarRow13019.table (sourceIndex j)).upper ∧
    (scalarRow13019.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13019.table (sourceIndex j)).centre) /
      (scalarRow13019.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13019.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13019,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13019,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13019,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13019,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13019,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13019,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13019,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13019,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13019,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13019,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13019,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13019,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13019,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13019,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13019,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13019,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13019,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13019,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13019,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13019,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13019,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13019,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13019,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13019,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13019,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13019,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13019,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13019,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13019,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13019,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13019,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13019,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13019,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13019,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13019,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13019,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13019,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13019,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13019,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13019,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13019,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13019,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13019,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13019,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13019,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13019,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13019,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13019,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13019,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13019,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13019,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13019,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13019,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13019,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13019,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13019,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13019,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13019,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13019,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13019,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13019,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13019,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13019,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13019,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13019,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13019,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13019,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13019,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13019,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13019,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13019,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13019,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13019,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13019,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13019,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13019,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13019,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13019,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13019,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13019,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13019,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13019,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13019,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13019,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13019,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13019,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13019 : FrameRepair 13019 scalarRow13019 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13019Cells j).1 (repair13019Cells j).2.1
  endpoint_upper := fun j => ((repair13019Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13019Cells j).2.2

theorem repair13020Cells (j : Fin 43) :
    0 ≤ (scalarRow13020.table (sourceIndex j)).upper ∧
    (scalarRow13020.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13020.table (sourceIndex j)).centre) /
      (scalarRow13020.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13020.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13020,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13020,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13020,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13020,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13020,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13020,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13020,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13020,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13020,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13020,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13020,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13020,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13020,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13020,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13020,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13020,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13020,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13020,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13020,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13020,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13020,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13020,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13020,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13020,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13020,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13020,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13020,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13020,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13020,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13020,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13020,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13020,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13020,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13020,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13020,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13020,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13020,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13020,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13020,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13020,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13020,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13020,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13020,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13020,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13020,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13020,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13020,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13020,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13020,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13020,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13020,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13020,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13020,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13020,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13020,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13020,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13020,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13020,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13020,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13020,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13020,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13020,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13020,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13020,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13020,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13020,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13020,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13020,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13020,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13020,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13020,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13020,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13020,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13020,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13020,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13020,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13020,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13020,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13020,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13020,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13020,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13020,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13020,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13020,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13020,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13020,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13020 : FrameRepair 13020 scalarRow13020 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13020Cells j).1 (repair13020Cells j).2.1
  endpoint_upper := fun j => ((repair13020Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13020Cells j).2.2

theorem repair13021Cells (j : Fin 43) :
    0 ≤ (scalarRow13021.table (sourceIndex j)).upper ∧
    (scalarRow13021.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13021.table (sourceIndex j)).centre) /
      (scalarRow13021.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13021.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13021,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13021,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13021,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13021,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13021,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13021,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13021,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13021,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13021,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13021,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13021,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13021,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13021,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13021,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13021,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13021,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13021,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13021,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13021,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13021,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13021,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13021,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13021,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13021,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13021,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13021,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13021,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13021,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13021,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13021,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13021,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13021,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13021,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13021,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13021,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13021,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13021,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13021,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13021,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13021,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13021,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13021,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13021,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13021,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13021,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13021,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13021,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13021,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13021,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13021,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13021,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13021,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13021,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13021,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13021,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13021,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13021,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13021,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13021,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13021,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13021,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13021,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13021,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13021,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13021,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13021,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13021,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13021,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13021,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13021,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13021,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13021,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13021,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13021,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13021,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13021,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13021,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13021,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13021,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13021,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13021,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13021,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13021,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13021,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13021,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13021,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13021 : FrameRepair 13021 scalarRow13021 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13021Cells j).1 (repair13021Cells j).2.1
  endpoint_upper := fun j => ((repair13021Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13021Cells j).2.2

theorem repair13022Cells (j : Fin 43) :
    0 ≤ (scalarRow13022.table (sourceIndex j)).upper ∧
    (scalarRow13022.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13022.table (sourceIndex j)).centre) /
      (scalarRow13022.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13022.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13022,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13022,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13022,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13022,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13022,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13022,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13022,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13022,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13022,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13022,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13022,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13022,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13022,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13022,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13022,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13022,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13022,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13022,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13022,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13022,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13022,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13022,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13022,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13022,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13022,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13022,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13022,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13022,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13022,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13022,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13022,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13022,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13022,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13022,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13022,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13022,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13022,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13022,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13022,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13022,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13022,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13022,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13022,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13022,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13022,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13022,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13022,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13022,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13022,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13022,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13022,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13022,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13022,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13022,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13022,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13022,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13022,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13022,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13022,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13022,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13022,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13022,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13022,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13022,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13022,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13022,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13022,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13022,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13022,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13022,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13022,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13022,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13022,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13022,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13022,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13022,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13022,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13022,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13022,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13022,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13022,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13022,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13022,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13022,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13022,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13022,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13022 : FrameRepair 13022 scalarRow13022 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13022Cells j).1 (repair13022Cells j).2.1
  endpoint_upper := fun j => ((repair13022Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13022Cells j).2.2

theorem repair13023Cells (j : Fin 43) :
    0 ≤ (scalarRow13023.table (sourceIndex j)).upper ∧
    (scalarRow13023.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13023.table (sourceIndex j)).centre) /
      (scalarRow13023.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13023.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13023,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13023,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13023,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13023,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13023,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13023,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13023,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13023,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13023,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13023,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13023,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13023,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13023,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13023,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13023,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13023,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13023,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13023,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13023,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13023,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13023,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13023,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13023,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13023,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13023,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13023,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13023,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13023,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13023,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13023,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13023,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13023,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13023,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13023,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13023,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13023,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13023,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13023,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13023,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13023,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13023,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13023,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13023,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13023,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13023,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13023,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13023,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13023,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13023,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13023,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13023,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13023,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13023,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13023,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13023,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13023,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13023,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13023,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13023,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13023,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13023,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13023,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13023,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13023,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13023,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13023,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13023,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13023,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13023,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13023,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13023,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13023,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13023,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13023,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13023,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13023,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13023,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13023,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13023,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13023,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13023,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13023,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13023,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13023,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13023,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13023,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13023 : FrameRepair 13023 scalarRow13023 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13023Cells j).1 (repair13023Cells j).2.1
  endpoint_upper := fun j => ((repair13023Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13023Cells j).2.2

theorem repair13024Cells (j : Fin 43) :
    0 ≤ (scalarRow13024.table (sourceIndex j)).upper ∧
    (scalarRow13024.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13024.table (sourceIndex j)).centre) /
      (scalarRow13024.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13024.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13024,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13024,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13024,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13024,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13024,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13024,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13024,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13024,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13024,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13024,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13024,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13024,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13024,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13024,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13024,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13024,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13024,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13024,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13024,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13024,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13024,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13024,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13024,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13024,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13024,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13024,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13024,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13024,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13024,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13024,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13024,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13024,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13024,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13024,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13024,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13024,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13024,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13024,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13024,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13024,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13024,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13024,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13024,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13024,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13024,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13024,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13024,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13024,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13024,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13024,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13024,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13024,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13024,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13024,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13024,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13024,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13024,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13024,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13024,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13024,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13024,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13024,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13024,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13024,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13024,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13024,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13024,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13024,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13024,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13024,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13024,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13024,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13024,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13024,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13024,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13024,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13024,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13024,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13024,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13024,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13024,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13024,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13024,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13024,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13024,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13024,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13024 : FrameRepair 13024 scalarRow13024 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13024Cells j).1 (repair13024Cells j).2.1
  endpoint_upper := fun j => ((repair13024Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13024Cells j).2.2

end BstLean.Part269
