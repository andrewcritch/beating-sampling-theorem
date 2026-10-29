import BstLean.Part269Rows18
import BstLean.Part269RepairCommon
namespace BstLean.Part269
open Real Set BstLean.Part255 BstLean.Part263 BstLean.Part264
theorem repair12800Cells (j : Fin 43) :
    0 ≤ (scalarRow12800.table (sourceIndex j)).upper ∧
    (scalarRow12800.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12800.table (sourceIndex j)).centre) /
      (scalarRow12800.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12800.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12800,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12800,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12800,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12800,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12800,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12800,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12800,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12800,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12800,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12800,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12800,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12800,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12800,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12800,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12800,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12800,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12800,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12800,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12800,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12800,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12800,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12800,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12800,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12800,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12800,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12800,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12800,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12800,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12800,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12800,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12800,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12800,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12800,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12800,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12800,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12800,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12800,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12800,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12800,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12800,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12800,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12800,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12800,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12800,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12800,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12800,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12800,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12800,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12800,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12800,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12800,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12800,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12800,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12800,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12800,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12800,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12800,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12800,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12800,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12800,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12800,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12800,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12800,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12800,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12800,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12800,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12800,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12800,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12800,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12800,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12800,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12800,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12800,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12800,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12800,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12800,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12800,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12800,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12800,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12800,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12800,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12800,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12800,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12800,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12800,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12800,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12800 : FrameRepair 12800 scalarRow12800 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12800Cells j).1 (repair12800Cells j).2.1
  endpoint_upper := fun j => ((repair12800Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12800Cells j).2.2

theorem repair12801Cells (j : Fin 43) :
    0 ≤ (scalarRow12801.table (sourceIndex j)).upper ∧
    (scalarRow12801.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12801.table (sourceIndex j)).centre) /
      (scalarRow12801.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12801.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12801,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12801,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12801,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12801,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12801,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12801,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12801,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12801,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12801,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12801,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12801,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12801,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12801,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12801,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12801,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12801,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12801,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12801,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12801,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12801,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12801,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12801,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12801,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12801,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12801,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12801,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12801,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12801,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12801,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12801,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12801,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12801,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12801,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12801,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12801,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12801,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12801,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12801,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12801,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12801,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12801,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12801,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12801,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12801,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12801,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12801,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12801,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12801,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12801,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12801,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12801,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12801,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12801,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12801,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12801,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12801,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12801,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12801,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12801,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12801,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12801,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12801,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12801,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12801,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12801,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12801,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12801,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12801,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12801,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12801,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12801,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12801,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12801,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12801,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12801,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12801,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12801,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12801,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12801,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12801,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12801,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12801,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12801,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12801,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12801,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12801,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12801 : FrameRepair 12801 scalarRow12801 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12801Cells j).1 (repair12801Cells j).2.1
  endpoint_upper := fun j => ((repair12801Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12801Cells j).2.2

theorem repair12802Cells (j : Fin 43) :
    0 ≤ (scalarRow12802.table (sourceIndex j)).upper ∧
    (scalarRow12802.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12802.table (sourceIndex j)).centre) /
      (scalarRow12802.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12802.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12802,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12802,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12802,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12802,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12802,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12802,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12802,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12802,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12802,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12802,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12802,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12802,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12802,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12802,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12802,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12802,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12802,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12802,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12802,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12802,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12802,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12802,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12802,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12802,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12802,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12802,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12802,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12802,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12802,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12802,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12802,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12802,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12802,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12802,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12802,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12802,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12802,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12802,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12802,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12802,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12802,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12802,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12802,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12802,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12802,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12802,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12802,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12802,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12802,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12802,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12802,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12802,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12802,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12802,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12802,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12802,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12802,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12802,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12802,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12802,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12802,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12802,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12802,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12802,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12802,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12802,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12802,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12802,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12802,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12802,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12802,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12802,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12802,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12802,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12802,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12802,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12802,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12802,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12802,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12802,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12802,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12802,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12802,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12802,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12802,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12802,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12802 : FrameRepair 12802 scalarRow12802 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12802Cells j).1 (repair12802Cells j).2.1
  endpoint_upper := fun j => ((repair12802Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12802Cells j).2.2

theorem repair12803Cells (j : Fin 43) :
    0 ≤ (scalarRow12803.table (sourceIndex j)).upper ∧
    (scalarRow12803.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12803.table (sourceIndex j)).centre) /
      (scalarRow12803.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12803.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12803,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12803,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12803,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12803,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12803,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12803,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12803,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12803,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12803,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12803,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12803,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12803,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12803,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12803,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12803,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12803,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12803,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12803,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12803,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12803,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12803,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12803,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12803,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12803,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12803,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12803,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12803,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12803,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12803,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12803,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12803,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12803,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12803,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12803,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12803,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12803,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12803,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12803,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12803,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12803,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12803,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12803,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12803,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12803,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12803,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12803,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12803,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12803,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12803,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12803,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12803,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12803,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12803,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12803,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12803,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12803,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12803,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12803,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12803,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12803,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12803,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12803,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12803,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12803,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12803,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12803,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12803,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12803,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12803,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12803,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12803,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12803,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12803,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12803,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12803,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12803,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12803,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12803,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12803,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12803,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12803,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12803,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12803,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12803,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12803,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12803,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12803 : FrameRepair 12803 scalarRow12803 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12803Cells j).1 (repair12803Cells j).2.1
  endpoint_upper := fun j => ((repair12803Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12803Cells j).2.2

theorem repair12804Cells (j : Fin 43) :
    0 ≤ (scalarRow12804.table (sourceIndex j)).upper ∧
    (scalarRow12804.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12804.table (sourceIndex j)).centre) /
      (scalarRow12804.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12804.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12804,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12804,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12804,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12804,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12804,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12804,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12804,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12804,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12804,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12804,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12804,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12804,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12804,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12804,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12804,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12804,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12804,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12804,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12804,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12804,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12804,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12804,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12804,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12804,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12804,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12804,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12804,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12804,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12804,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12804,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12804,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12804,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12804,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12804,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12804,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12804,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12804,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12804,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12804,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12804,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12804,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12804,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12804,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12804,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12804,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12804,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12804,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12804,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12804,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12804,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12804,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12804,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12804,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12804,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12804,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12804,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12804,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12804,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12804,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12804,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12804,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12804,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12804,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12804,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12804,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12804,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12804,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12804,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12804,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12804,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12804,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12804,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12804,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12804,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12804,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12804,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12804,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12804,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12804,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12804,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12804,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12804,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12804,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12804,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12804,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12804,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12804 : FrameRepair 12804 scalarRow12804 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12804Cells j).1 (repair12804Cells j).2.1
  endpoint_upper := fun j => ((repair12804Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12804Cells j).2.2

theorem repair12805Cells (j : Fin 43) :
    0 ≤ (scalarRow12805.table (sourceIndex j)).upper ∧
    (scalarRow12805.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12805.table (sourceIndex j)).centre) /
      (scalarRow12805.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12805.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12805,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12805,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12805,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12805,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12805,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12805,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12805,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12805,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12805,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12805,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12805,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12805,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12805,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12805,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12805,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12805,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12805,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12805,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12805,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12805,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12805,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12805,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12805,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12805,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12805,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12805,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12805,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12805,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12805,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12805,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12805,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12805,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12805,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12805,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12805,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12805,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12805,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12805,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12805,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12805,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12805,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12805,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12805,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12805,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12805,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12805,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12805,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12805,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12805,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12805,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12805,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12805,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12805,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12805,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12805,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12805,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12805,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12805,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12805,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12805,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12805,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12805,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12805,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12805,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12805,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12805,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12805,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12805,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12805,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12805,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12805,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12805,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12805,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12805,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12805,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12805,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12805,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12805,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12805,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12805,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12805,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12805,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12805,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12805,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12805,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12805,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12805 : FrameRepair 12805 scalarRow12805 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12805Cells j).1 (repair12805Cells j).2.1
  endpoint_upper := fun j => ((repair12805Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12805Cells j).2.2

theorem repair12806Cells (j : Fin 43) :
    0 ≤ (scalarRow12806.table (sourceIndex j)).upper ∧
    (scalarRow12806.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12806.table (sourceIndex j)).centre) /
      (scalarRow12806.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12806.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12806,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12806,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12806,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12806,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12806,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12806,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12806,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12806,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12806,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12806,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12806,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12806,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12806,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12806,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12806,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12806,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12806,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12806,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12806,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12806,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12806,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12806,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12806,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12806,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12806,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12806,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12806,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12806,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12806,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12806,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12806,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12806,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12806,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12806,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12806,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12806,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12806,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12806,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12806,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12806,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12806,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12806,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12806,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12806,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12806,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12806,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12806,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12806,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12806,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12806,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12806,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12806,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12806,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12806,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12806,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12806,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12806,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12806,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12806,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12806,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12806,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12806,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12806,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12806,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12806,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12806,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12806,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12806,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12806,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12806,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12806,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12806,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12806,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12806,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12806,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12806,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12806,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12806,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12806,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12806,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12806,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12806,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12806,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12806,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12806,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12806,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12806 : FrameRepair 12806 scalarRow12806 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12806Cells j).1 (repair12806Cells j).2.1
  endpoint_upper := fun j => ((repair12806Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12806Cells j).2.2

theorem repair12807Cells (j : Fin 43) :
    0 ≤ (scalarRow12807.table (sourceIndex j)).upper ∧
    (scalarRow12807.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12807.table (sourceIndex j)).centre) /
      (scalarRow12807.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12807.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12807,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12807,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12807,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12807,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12807,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12807,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12807,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12807,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12807,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12807,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12807,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12807,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12807,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12807,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12807,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12807,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12807,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12807,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12807,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12807,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12807,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12807,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12807,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12807,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12807,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12807,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12807,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12807,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12807,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12807,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12807,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12807,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12807,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12807,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12807,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12807,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12807,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12807,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12807,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12807,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12807,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12807,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12807,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12807,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12807,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12807,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12807,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12807,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12807,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12807,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12807,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12807,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12807,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12807,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12807,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12807,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12807,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12807,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12807,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12807,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12807,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12807,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12807,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12807,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12807,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12807,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12807,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12807,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12807,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12807,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12807,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12807,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12807,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12807,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12807,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12807,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12807,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12807,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12807,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12807,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12807,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12807,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12807,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12807,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12807,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12807,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12807 : FrameRepair 12807 scalarRow12807 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12807Cells j).1 (repair12807Cells j).2.1
  endpoint_upper := fun j => ((repair12807Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12807Cells j).2.2

theorem repair12808Cells (j : Fin 43) :
    0 ≤ (scalarRow12808.table (sourceIndex j)).upper ∧
    (scalarRow12808.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12808.table (sourceIndex j)).centre) /
      (scalarRow12808.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12808.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12808,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12808,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12808,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12808,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12808,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12808,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12808,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12808,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12808,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12808,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12808,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12808,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12808,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12808,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12808,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12808,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12808,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12808,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12808,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12808,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12808,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12808,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12808,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12808,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12808,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12808,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12808,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12808,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12808,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12808,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12808,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12808,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12808,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12808,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12808,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12808,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12808,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12808,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12808,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12808,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12808,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12808,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12808,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12808,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12808,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12808,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12808,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12808,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12808,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12808,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12808,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12808,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12808,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12808,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12808,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12808,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12808,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12808,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12808,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12808,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12808,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12808,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12808,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12808,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12808,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12808,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12808,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12808,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12808,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12808,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12808,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12808,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12808,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12808,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12808,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12808,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12808,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12808,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12808,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12808,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12808,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12808,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12808,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12808,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12808,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12808,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12808 : FrameRepair 12808 scalarRow12808 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12808Cells j).1 (repair12808Cells j).2.1
  endpoint_upper := fun j => ((repair12808Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12808Cells j).2.2

theorem repair12809Cells (j : Fin 43) :
    0 ≤ (scalarRow12809.table (sourceIndex j)).upper ∧
    (scalarRow12809.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12809.table (sourceIndex j)).centre) /
      (scalarRow12809.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12809.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12809,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12809,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12809,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12809,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12809,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12809,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12809,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12809,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12809,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12809,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12809,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12809,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12809,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12809,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12809,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12809,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12809,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12809,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12809,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12809,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12809,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12809,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12809,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12809,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12809,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12809,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12809,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12809,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12809,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12809,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12809,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12809,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12809,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12809,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12809,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12809,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12809,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12809,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12809,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12809,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12809,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12809,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12809,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12809,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12809,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12809,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12809,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12809,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12809,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12809,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12809,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12809,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12809,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12809,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12809,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12809,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12809,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12809,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12809,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12809,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12809,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12809,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12809,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12809,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12809,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12809,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12809,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12809,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12809,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12809,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12809,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12809,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12809,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12809,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12809,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12809,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12809,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12809,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12809,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12809,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12809,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12809,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12809,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12809,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12809,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12809,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12809 : FrameRepair 12809 scalarRow12809 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12809Cells j).1 (repair12809Cells j).2.1
  endpoint_upper := fun j => ((repair12809Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12809Cells j).2.2

theorem repair12810Cells (j : Fin 43) :
    0 ≤ (scalarRow12810.table (sourceIndex j)).upper ∧
    (scalarRow12810.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12810.table (sourceIndex j)).centre) /
      (scalarRow12810.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12810.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12810,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12810,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12810,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12810,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12810,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12810,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12810,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12810,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12810,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12810,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12810,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12810,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12810,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12810,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12810,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12810,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12810,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12810,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12810,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12810,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12810,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12810,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12810,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12810,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12810,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12810,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12810,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12810,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12810,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12810,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12810,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12810,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12810,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12810,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12810,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12810,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12810,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12810,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12810,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12810,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12810,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12810,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12810,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12810,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12810,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12810,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12810,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12810,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12810,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12810,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12810,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12810,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12810,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12810,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12810,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12810,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12810,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12810,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12810,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12810,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12810,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12810,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12810,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12810,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12810,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12810,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12810,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12810,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12810,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12810,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12810,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12810,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12810,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12810,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12810,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12810,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12810,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12810,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12810,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12810,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12810,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12810,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12810,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12810,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12810,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12810,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12810 : FrameRepair 12810 scalarRow12810 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12810Cells j).1 (repair12810Cells j).2.1
  endpoint_upper := fun j => ((repair12810Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12810Cells j).2.2

theorem repair12811Cells (j : Fin 43) :
    0 ≤ (scalarRow12811.table (sourceIndex j)).upper ∧
    (scalarRow12811.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12811.table (sourceIndex j)).centre) /
      (scalarRow12811.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12811.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12811,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12811,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12811,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12811,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12811,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12811,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12811,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12811,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12811,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12811,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12811,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12811,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12811,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12811,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12811,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12811,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12811,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12811,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12811,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12811,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12811,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12811,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12811,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12811,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12811,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12811,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12811,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12811,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12811,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12811,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12811,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12811,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12811,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12811,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12811,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12811,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12811,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12811,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12811,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12811,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12811,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12811,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12811,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12811,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12811,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12811,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12811,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12811,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12811,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12811,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12811,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12811,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12811,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12811,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12811,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12811,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12811,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12811,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12811,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12811,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12811,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12811,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12811,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12811,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12811,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12811,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12811,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12811,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12811,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12811,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12811,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12811,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12811,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12811,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12811,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12811,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12811,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12811,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12811,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12811,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12811,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12811,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12811,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12811,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12811,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12811,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12811 : FrameRepair 12811 scalarRow12811 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12811Cells j).1 (repair12811Cells j).2.1
  endpoint_upper := fun j => ((repair12811Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12811Cells j).2.2

theorem repair12812Cells (j : Fin 43) :
    0 ≤ (scalarRow12812.table (sourceIndex j)).upper ∧
    (scalarRow12812.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12812.table (sourceIndex j)).centre) /
      (scalarRow12812.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12812.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12812,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12812,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12812,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12812,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12812,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12812,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12812,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12812,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12812,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12812,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12812,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12812,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12812,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12812,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12812,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12812,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12812,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12812,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12812,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12812,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12812,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12812,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12812,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12812,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12812,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12812,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12812,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12812,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12812,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12812,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12812,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12812,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12812,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12812,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12812,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12812,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12812,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12812,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12812,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12812,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12812,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12812,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12812,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12812,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12812,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12812,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12812,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12812,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12812,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12812,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12812,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12812,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12812,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12812,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12812,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12812,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12812,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12812,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12812,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12812,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12812,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12812,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12812,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12812,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12812,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12812,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12812,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12812,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12812,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12812,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12812,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12812,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12812,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12812,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12812,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12812,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12812,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12812,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12812,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12812,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12812,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12812,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12812,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12812,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12812,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12812,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12812 : FrameRepair 12812 scalarRow12812 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12812Cells j).1 (repair12812Cells j).2.1
  endpoint_upper := fun j => ((repair12812Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12812Cells j).2.2

theorem repair12813Cells (j : Fin 43) :
    0 ≤ (scalarRow12813.table (sourceIndex j)).upper ∧
    (scalarRow12813.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12813.table (sourceIndex j)).centre) /
      (scalarRow12813.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12813.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12813,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12813,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12813,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12813,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12813,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12813,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12813,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12813,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12813,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12813,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12813,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12813,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12813,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12813,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12813,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12813,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12813,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12813,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12813,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12813,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12813,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12813,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12813,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12813,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12813,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12813,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12813,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12813,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12813,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12813,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12813,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12813,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12813,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12813,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12813,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12813,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12813,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12813,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12813,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12813,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12813,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12813,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12813,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12813,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12813,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12813,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12813,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12813,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12813,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12813,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12813,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12813,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12813,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12813,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12813,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12813,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12813,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12813,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12813,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12813,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12813,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12813,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12813,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12813,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12813,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12813,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12813,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12813,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12813,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12813,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12813,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12813,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12813,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12813,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12813,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12813,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12813,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12813,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12813,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12813,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12813,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12813,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12813,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12813,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12813,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12813,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12813 : FrameRepair 12813 scalarRow12813 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12813Cells j).1 (repair12813Cells j).2.1
  endpoint_upper := fun j => ((repair12813Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12813Cells j).2.2

theorem repair12814Cells (j : Fin 43) :
    0 ≤ (scalarRow12814.table (sourceIndex j)).upper ∧
    (scalarRow12814.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12814.table (sourceIndex j)).centre) /
      (scalarRow12814.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12814.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12814,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12814,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12814,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12814,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12814,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12814,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12814,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12814,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12814,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12814,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12814,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12814,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12814,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12814,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12814,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12814,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12814,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12814,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12814,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12814,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12814,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12814,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12814,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12814,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12814,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12814,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12814,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12814,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12814,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12814,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12814,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12814,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12814,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12814,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12814,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12814,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12814,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12814,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12814,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12814,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12814,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12814,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12814,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12814,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12814,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12814,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12814,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12814,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12814,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12814,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12814,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12814,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12814,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12814,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12814,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12814,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12814,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12814,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12814,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12814,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12814,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12814,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12814,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12814,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12814,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12814,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12814,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12814,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12814,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12814,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12814,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12814,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12814,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12814,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12814,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12814,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12814,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12814,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12814,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12814,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12814,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12814,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12814,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12814,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12814,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12814,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12814 : FrameRepair 12814 scalarRow12814 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12814Cells j).1 (repair12814Cells j).2.1
  endpoint_upper := fun j => ((repair12814Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12814Cells j).2.2

theorem repair12815Cells (j : Fin 43) :
    0 ≤ (scalarRow12815.table (sourceIndex j)).upper ∧
    (scalarRow12815.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12815.table (sourceIndex j)).centre) /
      (scalarRow12815.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12815.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12815,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12815,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12815,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12815,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12815,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12815,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12815,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12815,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12815,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12815,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12815,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12815,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12815,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12815,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12815,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12815,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12815,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12815,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12815,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12815,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12815,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12815,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12815,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12815,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12815,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12815,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12815,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12815,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12815,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12815,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12815,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12815,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12815,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12815,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12815,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12815,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12815,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12815,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12815,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12815,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12815,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12815,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12815,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12815,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12815,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12815,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12815,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12815,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12815,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12815,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12815,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12815,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12815,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12815,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12815,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12815,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12815,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12815,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12815,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12815,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12815,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12815,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12815,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12815,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12815,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12815,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12815,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12815,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12815,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12815,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12815,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12815,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12815,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12815,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12815,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12815,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12815,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12815,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12815,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12815,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12815,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12815,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12815,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12815,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12815,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12815,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12815 : FrameRepair 12815 scalarRow12815 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12815Cells j).1 (repair12815Cells j).2.1
  endpoint_upper := fun j => ((repair12815Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12815Cells j).2.2

theorem repair12816Cells (j : Fin 43) :
    0 ≤ (scalarRow12816.table (sourceIndex j)).upper ∧
    (scalarRow12816.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12816.table (sourceIndex j)).centre) /
      (scalarRow12816.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12816.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12816,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12816,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12816,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12816,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12816,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12816,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12816,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12816,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12816,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12816,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12816,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12816,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12816,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12816,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12816,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12816,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12816,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12816,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12816,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12816,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12816,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12816,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12816,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12816,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12816,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12816,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12816,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12816,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12816,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12816,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12816,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12816,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12816,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12816,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12816,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12816,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12816,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12816,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12816,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12816,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12816,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12816,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12816,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12816,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12816,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12816,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12816,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12816,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12816,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12816,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12816,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12816,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12816,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12816,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12816,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12816,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12816,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12816,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12816,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12816,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12816,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12816,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12816,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12816,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12816,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12816,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12816,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12816,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12816,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12816,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12816,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12816,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12816,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12816,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12816,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12816,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12816,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12816,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12816,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12816,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12816,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12816,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12816,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12816,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12816,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12816,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12816 : FrameRepair 12816 scalarRow12816 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12816Cells j).1 (repair12816Cells j).2.1
  endpoint_upper := fun j => ((repair12816Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12816Cells j).2.2

theorem repair12817Cells (j : Fin 43) :
    0 ≤ (scalarRow12817.table (sourceIndex j)).upper ∧
    (scalarRow12817.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12817.table (sourceIndex j)).centre) /
      (scalarRow12817.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12817.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12817,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12817,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12817,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12817,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12817,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12817,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12817,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12817,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12817,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12817,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12817,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12817,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12817,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12817,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12817,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12817,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12817,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12817,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12817,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12817,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12817,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12817,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12817,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12817,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12817,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12817,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12817,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12817,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12817,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12817,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12817,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12817,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12817,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12817,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12817,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12817,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12817,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12817,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12817,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12817,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12817,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12817,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12817,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12817,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12817,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12817,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12817,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12817,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12817,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12817,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12817,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12817,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12817,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12817,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12817,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12817,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12817,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12817,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12817,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12817,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12817,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12817,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12817,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12817,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12817,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12817,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12817,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12817,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12817,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12817,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12817,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12817,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12817,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12817,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12817,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12817,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12817,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12817,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12817,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12817,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12817,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12817,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12817,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12817,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12817,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12817,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12817 : FrameRepair 12817 scalarRow12817 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12817Cells j).1 (repair12817Cells j).2.1
  endpoint_upper := fun j => ((repair12817Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12817Cells j).2.2

theorem repair12818Cells (j : Fin 43) :
    0 ≤ (scalarRow12818.table (sourceIndex j)).upper ∧
    (scalarRow12818.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12818.table (sourceIndex j)).centre) /
      (scalarRow12818.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12818.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12818,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12818,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12818,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12818,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12818,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12818,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12818,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12818,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12818,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12818,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12818,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12818,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12818,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12818,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12818,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12818,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12818,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12818,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12818,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12818,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12818,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12818,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12818,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12818,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12818,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12818,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12818,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12818,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12818,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12818,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12818,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12818,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12818,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12818,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12818,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12818,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12818,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12818,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12818,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12818,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12818,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12818,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12818,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12818,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12818,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12818,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12818,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12818,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12818,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12818,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12818,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12818,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12818,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12818,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12818,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12818,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12818,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12818,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12818,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12818,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12818,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12818,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12818,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12818,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12818,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12818,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12818,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12818,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12818,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12818,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12818,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12818,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12818,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12818,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12818,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12818,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12818,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12818,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12818,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12818,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12818,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12818,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12818,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12818,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12818,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12818,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12818 : FrameRepair 12818 scalarRow12818 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12818Cells j).1 (repair12818Cells j).2.1
  endpoint_upper := fun j => ((repair12818Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12818Cells j).2.2

theorem repair12819Cells (j : Fin 43) :
    0 ≤ (scalarRow12819.table (sourceIndex j)).upper ∧
    (scalarRow12819.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12819.table (sourceIndex j)).centre) /
      (scalarRow12819.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12819.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12819,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12819,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12819,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12819,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12819,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12819,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12819,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12819,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12819,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12819,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12819,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12819,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12819,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12819,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12819,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12819,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12819,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12819,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12819,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12819,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12819,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12819,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12819,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12819,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12819,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12819,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12819,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12819,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12819,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12819,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12819,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12819,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12819,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12819,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12819,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12819,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12819,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12819,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12819,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12819,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12819,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12819,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12819,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12819,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12819,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12819,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12819,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12819,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12819,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12819,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12819,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12819,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12819,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12819,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12819,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12819,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12819,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12819,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12819,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12819,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12819,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12819,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12819,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12819,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12819,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12819,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12819,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12819,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12819,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12819,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12819,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12819,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12819,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12819,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12819,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12819,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12819,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12819,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12819,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12819,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12819,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12819,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12819,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12819,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12819,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12819,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12819 : FrameRepair 12819 scalarRow12819 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12819Cells j).1 (repair12819Cells j).2.1
  endpoint_upper := fun j => ((repair12819Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12819Cells j).2.2

theorem repair12820Cells (j : Fin 43) :
    0 ≤ (scalarRow12820.table (sourceIndex j)).upper ∧
    (scalarRow12820.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12820.table (sourceIndex j)).centre) /
      (scalarRow12820.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12820.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12820,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12820,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12820,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12820,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12820,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12820,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12820,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12820,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12820,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12820,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12820,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12820,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12820,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12820,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12820,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12820,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12820,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12820,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12820,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12820,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12820,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12820,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12820,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12820,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12820,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12820,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12820,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12820,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12820,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12820,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12820,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12820,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12820,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12820,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12820,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12820,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12820,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12820,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12820,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12820,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12820,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12820,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12820,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12820,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12820,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12820,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12820,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12820,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12820,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12820,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12820,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12820,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12820,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12820,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12820,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12820,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12820,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12820,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12820,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12820,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12820,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12820,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12820,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12820,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12820,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12820,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12820,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12820,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12820,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12820,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12820,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12820,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12820,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12820,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12820,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12820,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12820,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12820,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12820,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12820,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12820,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12820,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12820,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12820,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12820,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12820,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12820 : FrameRepair 12820 scalarRow12820 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12820Cells j).1 (repair12820Cells j).2.1
  endpoint_upper := fun j => ((repair12820Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12820Cells j).2.2

theorem repair12821Cells (j : Fin 43) :
    0 ≤ (scalarRow12821.table (sourceIndex j)).upper ∧
    (scalarRow12821.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12821.table (sourceIndex j)).centre) /
      (scalarRow12821.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12821.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12821,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12821,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12821,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12821,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12821,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12821,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12821,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12821,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12821,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12821,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12821,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12821,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12821,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12821,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12821,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12821,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12821,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12821,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12821,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12821,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12821,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12821,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12821,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12821,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12821,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12821,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12821,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12821,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12821,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12821,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12821,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12821,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12821,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12821,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12821,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12821,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12821,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12821,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12821,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12821,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12821,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12821,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12821,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12821,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12821,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12821,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12821,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12821,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12821,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12821,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12821,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12821,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12821,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12821,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12821,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12821,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12821,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12821,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12821,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12821,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12821,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12821,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12821,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12821,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12821,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12821,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12821,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12821,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12821,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12821,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12821,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12821,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12821,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12821,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12821,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12821,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12821,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12821,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12821,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12821,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12821,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12821,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12821,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12821,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12821,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12821,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12821 : FrameRepair 12821 scalarRow12821 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12821Cells j).1 (repair12821Cells j).2.1
  endpoint_upper := fun j => ((repair12821Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12821Cells j).2.2

theorem repair12822Cells (j : Fin 43) :
    0 ≤ (scalarRow12822.table (sourceIndex j)).upper ∧
    (scalarRow12822.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12822.table (sourceIndex j)).centre) /
      (scalarRow12822.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12822.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12822,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12822,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12822,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12822,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12822,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12822,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12822,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12822,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12822,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12822,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12822,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12822,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12822,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12822,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12822,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12822,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12822,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12822,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12822,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12822,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12822,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12822,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12822,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12822,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12822,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12822,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12822,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12822,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12822,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12822,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12822,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12822,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12822,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12822,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12822,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12822,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12822,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12822,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12822,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12822,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12822,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12822,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12822,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12822,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12822,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12822,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12822,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12822,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12822,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12822,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12822,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12822,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12822,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12822,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12822,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12822,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12822,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12822,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12822,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12822,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12822,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12822,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12822,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12822,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12822,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12822,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12822,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12822,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12822,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12822,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12822,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12822,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12822,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12822,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12822,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12822,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12822,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12822,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12822,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12822,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12822,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12822,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12822,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12822,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12822,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12822,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12822 : FrameRepair 12822 scalarRow12822 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12822Cells j).1 (repair12822Cells j).2.1
  endpoint_upper := fun j => ((repair12822Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12822Cells j).2.2

theorem repair12823Cells (j : Fin 43) :
    0 ≤ (scalarRow12823.table (sourceIndex j)).upper ∧
    (scalarRow12823.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12823.table (sourceIndex j)).centre) /
      (scalarRow12823.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12823.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12823,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12823,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12823,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12823,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12823,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12823,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12823,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12823,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12823,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12823,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12823,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12823,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12823,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12823,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12823,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12823,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12823,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12823,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12823,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12823,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12823,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12823,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12823,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12823,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12823,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12823,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12823,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12823,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12823,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12823,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12823,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12823,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12823,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12823,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12823,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12823,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12823,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12823,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12823,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12823,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12823,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12823,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12823,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12823,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12823,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12823,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12823,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12823,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12823,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12823,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12823,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12823,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12823,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12823,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12823,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12823,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12823,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12823,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12823,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12823,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12823,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12823,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12823,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12823,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12823,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12823,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12823,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12823,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12823,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12823,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12823,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12823,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12823,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12823,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12823,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12823,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12823,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12823,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12823,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12823,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12823,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12823,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12823,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12823,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12823,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12823,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12823 : FrameRepair 12823 scalarRow12823 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12823Cells j).1 (repair12823Cells j).2.1
  endpoint_upper := fun j => ((repair12823Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12823Cells j).2.2

theorem repair12824Cells (j : Fin 43) :
    0 ≤ (scalarRow12824.table (sourceIndex j)).upper ∧
    (scalarRow12824.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12824.table (sourceIndex j)).centre) /
      (scalarRow12824.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12824.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12824,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12824,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12824,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12824,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12824,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12824,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12824,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12824,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12824,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12824,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12824,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12824,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12824,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12824,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12824,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12824,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12824,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12824,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12824,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12824,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12824,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12824,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12824,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12824,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12824,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12824,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12824,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12824,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12824,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12824,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12824,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12824,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12824,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12824,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12824,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12824,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12824,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12824,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12824,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12824,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12824,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12824,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12824,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12824,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12824,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12824,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12824,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12824,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12824,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12824,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12824,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12824,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12824,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12824,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12824,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12824,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12824,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12824,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12824,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12824,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12824,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12824,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12824,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12824,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12824,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12824,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12824,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12824,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12824,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12824,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12824,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12824,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12824,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12824,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12824,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12824,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12824,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12824,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12824,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12824,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12824,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12824,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12824,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12824,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12824,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12824,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12824 : FrameRepair 12824 scalarRow12824 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12824Cells j).1 (repair12824Cells j).2.1
  endpoint_upper := fun j => ((repair12824Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12824Cells j).2.2

end BstLean.Part269
