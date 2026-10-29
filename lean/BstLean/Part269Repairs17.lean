import BstLean.Part269Rows17
import BstLean.Part269RepairCommon
namespace BstLean.Part269
open Real Set BstLean.Part255 BstLean.Part263 BstLean.Part264
theorem repair12775Cells (j : Fin 43) :
    0 ≤ (scalarRow12775.table (sourceIndex j)).upper ∧
    (scalarRow12775.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12775.table (sourceIndex j)).centre) /
      (scalarRow12775.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12775.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12775,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12775,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12775,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12775,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12775,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12775,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12775,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12775,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12775,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12775,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12775,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12775,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12775,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12775,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12775,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12775,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12775,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12775,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12775,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12775,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12775,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12775,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12775,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12775,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12775,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12775,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12775,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12775,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12775,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12775,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12775,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12775,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12775,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12775,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12775,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12775,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12775,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12775,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12775,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12775,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12775,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12775,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12775,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12775,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12775,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12775,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12775,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12775,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12775,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12775,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12775,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12775,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12775,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12775,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12775,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12775,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12775,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12775,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12775,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12775,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12775,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12775,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12775,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12775,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12775,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12775,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12775,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12775,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12775,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12775,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12775,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12775,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12775,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12775,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12775,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12775,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12775,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12775,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12775,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12775,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12775,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12775,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12775,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12775,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12775,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12775,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12775 : FrameRepair 12775 scalarRow12775 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12775Cells j).1 (repair12775Cells j).2.1
  endpoint_upper := fun j => ((repair12775Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12775Cells j).2.2

theorem repair12776Cells (j : Fin 43) :
    0 ≤ (scalarRow12776.table (sourceIndex j)).upper ∧
    (scalarRow12776.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12776.table (sourceIndex j)).centre) /
      (scalarRow12776.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12776.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12776,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12776,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12776,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12776,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12776,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12776,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12776,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12776,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12776,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12776,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12776,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12776,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12776,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12776,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12776,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12776,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12776,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12776,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12776,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12776,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12776,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12776,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12776,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12776,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12776,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12776,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12776,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12776,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12776,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12776,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12776,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12776,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12776,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12776,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12776,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12776,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12776,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12776,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12776,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12776,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12776,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12776,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12776,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12776,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12776,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12776,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12776,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12776,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12776,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12776,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12776,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12776,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12776,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12776,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12776,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12776,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12776,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12776,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12776,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12776,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12776,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12776,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12776,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12776,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12776,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12776,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12776,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12776,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12776,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12776,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12776,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12776,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12776,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12776,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12776,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12776,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12776,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12776,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12776,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12776,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12776,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12776,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12776,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12776,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12776,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12776,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12776 : FrameRepair 12776 scalarRow12776 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12776Cells j).1 (repair12776Cells j).2.1
  endpoint_upper := fun j => ((repair12776Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12776Cells j).2.2

theorem repair12777Cells (j : Fin 43) :
    0 ≤ (scalarRow12777.table (sourceIndex j)).upper ∧
    (scalarRow12777.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12777.table (sourceIndex j)).centre) /
      (scalarRow12777.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12777.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12777,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12777,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12777,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12777,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12777,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12777,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12777,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12777,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12777,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12777,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12777,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12777,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12777,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12777,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12777,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12777,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12777,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12777,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12777,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12777,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12777,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12777,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12777,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12777,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12777,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12777,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12777,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12777,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12777,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12777,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12777,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12777,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12777,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12777,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12777,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12777,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12777,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12777,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12777,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12777,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12777,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12777,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12777,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12777,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12777,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12777,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12777,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12777,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12777,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12777,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12777,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12777,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12777,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12777,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12777,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12777,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12777,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12777,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12777,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12777,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12777,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12777,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12777,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12777,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12777,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12777,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12777,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12777,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12777,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12777,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12777,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12777,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12777,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12777,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12777,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12777,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12777,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12777,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12777,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12777,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12777,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12777,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12777,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12777,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12777,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12777,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12777 : FrameRepair 12777 scalarRow12777 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12777Cells j).1 (repair12777Cells j).2.1
  endpoint_upper := fun j => ((repair12777Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12777Cells j).2.2

theorem repair12778Cells (j : Fin 43) :
    0 ≤ (scalarRow12778.table (sourceIndex j)).upper ∧
    (scalarRow12778.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12778.table (sourceIndex j)).centre) /
      (scalarRow12778.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12778.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12778,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12778,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12778,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12778,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12778,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12778,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12778,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12778,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12778,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12778,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12778,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12778,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12778,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12778,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12778,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12778,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12778,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12778,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12778,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12778,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12778,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12778,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12778,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12778,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12778,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12778,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12778,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12778,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12778,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12778,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12778,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12778,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12778,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12778,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12778,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12778,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12778,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12778,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12778,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12778,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12778,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12778,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12778,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12778,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12778,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12778,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12778,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12778,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12778,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12778,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12778,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12778,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12778,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12778,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12778,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12778,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12778,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12778,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12778,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12778,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12778,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12778,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12778,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12778,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12778,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12778,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12778,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12778,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12778,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12778,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12778,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12778,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12778,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12778,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12778,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12778,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12778,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12778,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12778,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12778,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12778,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12778,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12778,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12778,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12778,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12778,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12778 : FrameRepair 12778 scalarRow12778 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12778Cells j).1 (repair12778Cells j).2.1
  endpoint_upper := fun j => ((repair12778Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12778Cells j).2.2

theorem repair12779Cells (j : Fin 43) :
    0 ≤ (scalarRow12779.table (sourceIndex j)).upper ∧
    (scalarRow12779.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12779.table (sourceIndex j)).centre) /
      (scalarRow12779.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12779.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12779,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12779,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12779,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12779,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12779,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12779,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12779,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12779,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12779,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12779,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12779,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12779,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12779,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12779,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12779,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12779,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12779,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12779,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12779,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12779,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12779,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12779,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12779,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12779,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12779,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12779,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12779,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12779,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12779,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12779,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12779,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12779,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12779,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12779,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12779,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12779,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12779,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12779,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12779,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12779,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12779,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12779,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12779,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12779,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12779,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12779,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12779,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12779,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12779,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12779,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12779,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12779,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12779,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12779,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12779,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12779,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12779,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12779,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12779,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12779,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12779,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12779,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12779,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12779,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12779,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12779,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12779,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12779,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12779,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12779,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12779,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12779,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12779,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12779,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12779,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12779,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12779,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12779,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12779,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12779,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12779,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12779,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12779,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12779,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12779,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12779,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12779 : FrameRepair 12779 scalarRow12779 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12779Cells j).1 (repair12779Cells j).2.1
  endpoint_upper := fun j => ((repair12779Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12779Cells j).2.2

theorem repair12780Cells (j : Fin 43) :
    0 ≤ (scalarRow12780.table (sourceIndex j)).upper ∧
    (scalarRow12780.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12780.table (sourceIndex j)).centre) /
      (scalarRow12780.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12780.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12780,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12780,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12780,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12780,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12780,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12780,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12780,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12780,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12780,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12780,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12780,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12780,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12780,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12780,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12780,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12780,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12780,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12780,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12780,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12780,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12780,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12780,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12780,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12780,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12780,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12780,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12780,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12780,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12780,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12780,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12780,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12780,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12780,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12780,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12780,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12780,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12780,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12780,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12780,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12780,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12780,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12780,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12780,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12780,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12780,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12780,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12780,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12780,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12780,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12780,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12780,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12780,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12780,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12780,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12780,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12780,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12780,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12780,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12780,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12780,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12780,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12780,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12780,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12780,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12780,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12780,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12780,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12780,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12780,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12780,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12780,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12780,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12780,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12780,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12780,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12780,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12780,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12780,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12780,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12780,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12780,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12780,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12780,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12780,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12780,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12780,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12780 : FrameRepair 12780 scalarRow12780 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12780Cells j).1 (repair12780Cells j).2.1
  endpoint_upper := fun j => ((repair12780Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12780Cells j).2.2

theorem repair12781Cells (j : Fin 43) :
    0 ≤ (scalarRow12781.table (sourceIndex j)).upper ∧
    (scalarRow12781.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12781.table (sourceIndex j)).centre) /
      (scalarRow12781.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12781.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12781,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12781,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12781,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12781,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12781,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12781,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12781,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12781,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12781,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12781,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12781,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12781,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12781,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12781,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12781,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12781,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12781,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12781,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12781,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12781,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12781,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12781,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12781,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12781,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12781,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12781,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12781,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12781,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12781,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12781,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12781,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12781,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12781,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12781,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12781,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12781,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12781,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12781,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12781,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12781,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12781,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12781,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12781,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12781,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12781,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12781,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12781,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12781,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12781,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12781,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12781,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12781,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12781,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12781,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12781,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12781,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12781,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12781,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12781,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12781,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12781,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12781,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12781,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12781,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12781,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12781,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12781,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12781,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12781,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12781,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12781,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12781,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12781,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12781,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12781,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12781,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12781,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12781,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12781,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12781,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12781,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12781,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12781,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12781,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12781,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12781,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12781 : FrameRepair 12781 scalarRow12781 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12781Cells j).1 (repair12781Cells j).2.1
  endpoint_upper := fun j => ((repair12781Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12781Cells j).2.2

theorem repair12782Cells (j : Fin 43) :
    0 ≤ (scalarRow12782.table (sourceIndex j)).upper ∧
    (scalarRow12782.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12782.table (sourceIndex j)).centre) /
      (scalarRow12782.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12782.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12782,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12782,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12782,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12782,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12782,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12782,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12782,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12782,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12782,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12782,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12782,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12782,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12782,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12782,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12782,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12782,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12782,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12782,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12782,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12782,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12782,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12782,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12782,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12782,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12782,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12782,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12782,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12782,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12782,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12782,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12782,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12782,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12782,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12782,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12782,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12782,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12782,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12782,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12782,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12782,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12782,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12782,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12782,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12782,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12782,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12782,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12782,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12782,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12782,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12782,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12782,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12782,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12782,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12782,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12782,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12782,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12782,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12782,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12782,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12782,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12782,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12782,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12782,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12782,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12782,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12782,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12782,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12782,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12782,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12782,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12782,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12782,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12782,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12782,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12782,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12782,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12782,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12782,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12782,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12782,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12782,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12782,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12782,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12782,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12782,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12782,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12782 : FrameRepair 12782 scalarRow12782 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12782Cells j).1 (repair12782Cells j).2.1
  endpoint_upper := fun j => ((repair12782Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12782Cells j).2.2

theorem repair12783Cells (j : Fin 43) :
    0 ≤ (scalarRow12783.table (sourceIndex j)).upper ∧
    (scalarRow12783.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12783.table (sourceIndex j)).centre) /
      (scalarRow12783.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12783.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12783,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12783,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12783,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12783,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12783,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12783,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12783,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12783,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12783,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12783,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12783,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12783,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12783,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12783,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12783,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12783,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12783,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12783,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12783,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12783,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12783,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12783,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12783,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12783,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12783,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12783,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12783,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12783,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12783,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12783,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12783,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12783,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12783,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12783,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12783,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12783,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12783,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12783,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12783,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12783,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12783,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12783,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12783,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12783,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12783,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12783,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12783,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12783,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12783,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12783,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12783,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12783,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12783,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12783,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12783,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12783,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12783,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12783,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12783,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12783,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12783,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12783,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12783,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12783,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12783,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12783,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12783,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12783,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12783,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12783,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12783,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12783,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12783,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12783,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12783,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12783,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12783,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12783,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12783,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12783,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12783,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12783,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12783,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12783,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12783,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12783,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12783 : FrameRepair 12783 scalarRow12783 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12783Cells j).1 (repair12783Cells j).2.1
  endpoint_upper := fun j => ((repair12783Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12783Cells j).2.2

theorem repair12784Cells (j : Fin 43) :
    0 ≤ (scalarRow12784.table (sourceIndex j)).upper ∧
    (scalarRow12784.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12784.table (sourceIndex j)).centre) /
      (scalarRow12784.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12784.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12784,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12784,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12784,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12784,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12784,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12784,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12784,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12784,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12784,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12784,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12784,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12784,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12784,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12784,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12784,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12784,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12784,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12784,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12784,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12784,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12784,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12784,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12784,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12784,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12784,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12784,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12784,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12784,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12784,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12784,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12784,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12784,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12784,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12784,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12784,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12784,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12784,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12784,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12784,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12784,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12784,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12784,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12784,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12784,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12784,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12784,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12784,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12784,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12784,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12784,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12784,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12784,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12784,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12784,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12784,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12784,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12784,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12784,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12784,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12784,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12784,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12784,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12784,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12784,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12784,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12784,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12784,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12784,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12784,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12784,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12784,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12784,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12784,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12784,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12784,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12784,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12784,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12784,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12784,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12784,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12784,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12784,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12784,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12784,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12784,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12784,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12784 : FrameRepair 12784 scalarRow12784 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12784Cells j).1 (repair12784Cells j).2.1
  endpoint_upper := fun j => ((repair12784Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12784Cells j).2.2

theorem repair12785Cells (j : Fin 43) :
    0 ≤ (scalarRow12785.table (sourceIndex j)).upper ∧
    (scalarRow12785.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12785.table (sourceIndex j)).centre) /
      (scalarRow12785.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12785.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12785,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12785,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12785,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12785,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12785,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12785,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12785,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12785,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12785,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12785,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12785,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12785,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12785,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12785,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12785,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12785,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12785,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12785,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12785,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12785,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12785,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12785,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12785,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12785,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12785,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12785,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12785,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12785,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12785,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12785,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12785,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12785,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12785,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12785,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12785,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12785,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12785,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12785,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12785,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12785,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12785,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12785,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12785,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12785,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12785,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12785,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12785,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12785,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12785,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12785,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12785,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12785,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12785,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12785,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12785,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12785,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12785,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12785,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12785,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12785,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12785,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12785,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12785,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12785,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12785,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12785,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12785,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12785,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12785,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12785,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12785,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12785,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12785,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12785,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12785,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12785,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12785,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12785,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12785,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12785,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12785,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12785,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12785,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12785,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12785,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12785,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12785 : FrameRepair 12785 scalarRow12785 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12785Cells j).1 (repair12785Cells j).2.1
  endpoint_upper := fun j => ((repair12785Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12785Cells j).2.2

theorem repair12786Cells (j : Fin 43) :
    0 ≤ (scalarRow12786.table (sourceIndex j)).upper ∧
    (scalarRow12786.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12786.table (sourceIndex j)).centre) /
      (scalarRow12786.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12786.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12786,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12786,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12786,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12786,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12786,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12786,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12786,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12786,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12786,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12786,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12786,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12786,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12786,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12786,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12786,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12786,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12786,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12786,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12786,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12786,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12786,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12786,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12786,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12786,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12786,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12786,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12786,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12786,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12786,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12786,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12786,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12786,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12786,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12786,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12786,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12786,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12786,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12786,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12786,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12786,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12786,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12786,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12786,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12786,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12786,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12786,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12786,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12786,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12786,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12786,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12786,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12786,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12786,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12786,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12786,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12786,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12786,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12786,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12786,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12786,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12786,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12786,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12786,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12786,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12786,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12786,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12786,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12786,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12786,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12786,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12786,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12786,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12786,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12786,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12786,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12786,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12786,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12786,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12786,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12786,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12786,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12786,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12786,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12786,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12786,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12786,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12786 : FrameRepair 12786 scalarRow12786 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12786Cells j).1 (repair12786Cells j).2.1
  endpoint_upper := fun j => ((repair12786Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12786Cells j).2.2

theorem repair12787Cells (j : Fin 43) :
    0 ≤ (scalarRow12787.table (sourceIndex j)).upper ∧
    (scalarRow12787.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12787.table (sourceIndex j)).centre) /
      (scalarRow12787.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12787.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12787,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12787,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12787,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12787,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12787,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12787,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12787,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12787,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12787,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12787,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12787,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12787,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12787,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12787,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12787,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12787,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12787,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12787,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12787,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12787,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12787,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12787,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12787,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12787,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12787,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12787,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12787,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12787,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12787,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12787,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12787,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12787,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12787,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12787,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12787,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12787,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12787,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12787,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12787,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12787,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12787,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12787,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12787,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12787,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12787,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12787,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12787,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12787,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12787,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12787,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12787,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12787,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12787,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12787,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12787,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12787,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12787,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12787,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12787,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12787,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12787,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12787,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12787,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12787,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12787,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12787,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12787,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12787,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12787,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12787,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12787,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12787,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12787,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12787,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12787,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12787,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12787,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12787,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12787,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12787,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12787,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12787,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12787,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12787,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12787,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12787,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12787 : FrameRepair 12787 scalarRow12787 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12787Cells j).1 (repair12787Cells j).2.1
  endpoint_upper := fun j => ((repair12787Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12787Cells j).2.2

theorem repair12788Cells (j : Fin 43) :
    0 ≤ (scalarRow12788.table (sourceIndex j)).upper ∧
    (scalarRow12788.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12788.table (sourceIndex j)).centre) /
      (scalarRow12788.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12788.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12788,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12788,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12788,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12788,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12788,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12788,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12788,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12788,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12788,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12788,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12788,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12788,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12788,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12788,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12788,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12788,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12788,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12788,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12788,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12788,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12788,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12788,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12788,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12788,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12788,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12788,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12788,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12788,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12788,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12788,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12788,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12788,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12788,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12788,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12788,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12788,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12788,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12788,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12788,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12788,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12788,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12788,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12788,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12788,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12788,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12788,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12788,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12788,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12788,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12788,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12788,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12788,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12788,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12788,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12788,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12788,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12788,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12788,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12788,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12788,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12788,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12788,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12788,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12788,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12788,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12788,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12788,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12788,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12788,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12788,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12788,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12788,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12788,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12788,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12788,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12788,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12788,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12788,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12788,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12788,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12788,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12788,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12788,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12788,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12788,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12788,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12788 : FrameRepair 12788 scalarRow12788 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12788Cells j).1 (repair12788Cells j).2.1
  endpoint_upper := fun j => ((repair12788Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12788Cells j).2.2

theorem repair12789Cells (j : Fin 43) :
    0 ≤ (scalarRow12789.table (sourceIndex j)).upper ∧
    (scalarRow12789.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12789.table (sourceIndex j)).centre) /
      (scalarRow12789.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12789.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12789,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12789,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12789,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12789,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12789,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12789,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12789,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12789,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12789,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12789,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12789,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12789,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12789,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12789,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12789,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12789,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12789,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12789,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12789,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12789,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12789,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12789,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12789,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12789,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12789,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12789,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12789,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12789,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12789,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12789,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12789,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12789,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12789,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12789,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12789,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12789,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12789,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12789,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12789,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12789,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12789,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12789,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12789,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12789,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12789,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12789,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12789,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12789,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12789,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12789,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12789,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12789,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12789,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12789,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12789,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12789,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12789,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12789,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12789,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12789,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12789,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12789,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12789,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12789,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12789,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12789,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12789,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12789,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12789,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12789,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12789,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12789,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12789,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12789,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12789,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12789,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12789,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12789,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12789,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12789,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12789,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12789,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12789,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12789,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12789,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12789,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12789 : FrameRepair 12789 scalarRow12789 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12789Cells j).1 (repair12789Cells j).2.1
  endpoint_upper := fun j => ((repair12789Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12789Cells j).2.2

theorem repair12790Cells (j : Fin 43) :
    0 ≤ (scalarRow12790.table (sourceIndex j)).upper ∧
    (scalarRow12790.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12790.table (sourceIndex j)).centre) /
      (scalarRow12790.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12790.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12790,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12790,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12790,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12790,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12790,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12790,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12790,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12790,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12790,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12790,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12790,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12790,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12790,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12790,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12790,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12790,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12790,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12790,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12790,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12790,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12790,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12790,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12790,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12790,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12790,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12790,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12790,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12790,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12790,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12790,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12790,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12790,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12790,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12790,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12790,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12790,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12790,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12790,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12790,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12790,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12790,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12790,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12790,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12790,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12790,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12790,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12790,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12790,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12790,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12790,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12790,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12790,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12790,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12790,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12790,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12790,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12790,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12790,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12790,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12790,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12790,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12790,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12790,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12790,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12790,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12790,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12790,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12790,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12790,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12790,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12790,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12790,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12790,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12790,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12790,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12790,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12790,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12790,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12790,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12790,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12790,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12790,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12790,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12790,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12790,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12790,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12790 : FrameRepair 12790 scalarRow12790 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12790Cells j).1 (repair12790Cells j).2.1
  endpoint_upper := fun j => ((repair12790Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12790Cells j).2.2

theorem repair12791Cells (j : Fin 43) :
    0 ≤ (scalarRow12791.table (sourceIndex j)).upper ∧
    (scalarRow12791.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12791.table (sourceIndex j)).centre) /
      (scalarRow12791.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12791.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12791,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12791,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12791,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12791,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12791,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12791,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12791,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12791,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12791,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12791,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12791,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12791,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12791,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12791,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12791,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12791,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12791,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12791,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12791,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12791,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12791,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12791,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12791,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12791,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12791,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12791,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12791,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12791,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12791,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12791,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12791,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12791,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12791,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12791,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12791,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12791,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12791,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12791,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12791,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12791,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12791,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12791,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12791,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12791,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12791,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12791,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12791,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12791,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12791,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12791,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12791,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12791,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12791,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12791,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12791,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12791,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12791,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12791,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12791,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12791,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12791,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12791,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12791,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12791,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12791,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12791,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12791,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12791,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12791,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12791,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12791,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12791,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12791,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12791,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12791,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12791,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12791,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12791,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12791,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12791,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12791,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12791,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12791,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12791,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12791,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12791,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12791 : FrameRepair 12791 scalarRow12791 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12791Cells j).1 (repair12791Cells j).2.1
  endpoint_upper := fun j => ((repair12791Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12791Cells j).2.2

theorem repair12792Cells (j : Fin 43) :
    0 ≤ (scalarRow12792.table (sourceIndex j)).upper ∧
    (scalarRow12792.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12792.table (sourceIndex j)).centre) /
      (scalarRow12792.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12792.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12792,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12792,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12792,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12792,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12792,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12792,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12792,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12792,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12792,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12792,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12792,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12792,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12792,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12792,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12792,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12792,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12792,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12792,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12792,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12792,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12792,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12792,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12792,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12792,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12792,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12792,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12792,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12792,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12792,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12792,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12792,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12792,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12792,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12792,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12792,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12792,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12792,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12792,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12792,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12792,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12792,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12792,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12792,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12792,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12792,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12792,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12792,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12792,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12792,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12792,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12792,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12792,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12792,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12792,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12792,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12792,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12792,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12792,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12792,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12792,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12792,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12792,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12792,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12792,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12792,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12792,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12792,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12792,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12792,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12792,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12792,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12792,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12792,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12792,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12792,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12792,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12792,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12792,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12792,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12792,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12792,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12792,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12792,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12792,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12792,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12792,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12792 : FrameRepair 12792 scalarRow12792 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12792Cells j).1 (repair12792Cells j).2.1
  endpoint_upper := fun j => ((repair12792Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12792Cells j).2.2

theorem repair12793Cells (j : Fin 43) :
    0 ≤ (scalarRow12793.table (sourceIndex j)).upper ∧
    (scalarRow12793.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12793.table (sourceIndex j)).centre) /
      (scalarRow12793.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12793.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12793,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12793,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12793,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12793,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12793,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12793,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12793,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12793,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12793,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12793,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12793,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12793,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12793,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12793,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12793,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12793,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12793,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12793,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12793,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12793,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12793,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12793,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12793,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12793,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12793,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12793,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12793,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12793,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12793,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12793,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12793,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12793,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12793,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12793,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12793,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12793,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12793,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12793,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12793,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12793,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12793,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12793,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12793,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12793,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12793,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12793,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12793,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12793,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12793,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12793,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12793,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12793,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12793,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12793,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12793,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12793,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12793,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12793,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12793,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12793,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12793,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12793,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12793,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12793,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12793,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12793,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12793,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12793,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12793,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12793,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12793,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12793,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12793,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12793,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12793,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12793,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12793,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12793,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12793,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12793,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12793,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12793,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12793,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12793,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12793,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12793,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12793 : FrameRepair 12793 scalarRow12793 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12793Cells j).1 (repair12793Cells j).2.1
  endpoint_upper := fun j => ((repair12793Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12793Cells j).2.2

theorem repair12794Cells (j : Fin 43) :
    0 ≤ (scalarRow12794.table (sourceIndex j)).upper ∧
    (scalarRow12794.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12794.table (sourceIndex j)).centre) /
      (scalarRow12794.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12794.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12794,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12794,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12794,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12794,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12794,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12794,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12794,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12794,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12794,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12794,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12794,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12794,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12794,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12794,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12794,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12794,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12794,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12794,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12794,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12794,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12794,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12794,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12794,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12794,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12794,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12794,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12794,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12794,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12794,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12794,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12794,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12794,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12794,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12794,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12794,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12794,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12794,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12794,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12794,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12794,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12794,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12794,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12794,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12794,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12794,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12794,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12794,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12794,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12794,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12794,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12794,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12794,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12794,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12794,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12794,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12794,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12794,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12794,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12794,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12794,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12794,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12794,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12794,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12794,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12794,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12794,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12794,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12794,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12794,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12794,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12794,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12794,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12794,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12794,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12794,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12794,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12794,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12794,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12794,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12794,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12794,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12794,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12794,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12794,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12794,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12794,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12794 : FrameRepair 12794 scalarRow12794 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12794Cells j).1 (repair12794Cells j).2.1
  endpoint_upper := fun j => ((repair12794Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12794Cells j).2.2

theorem repair12795Cells (j : Fin 43) :
    0 ≤ (scalarRow12795.table (sourceIndex j)).upper ∧
    (scalarRow12795.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12795.table (sourceIndex j)).centre) /
      (scalarRow12795.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12795.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12795,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12795,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12795,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12795,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12795,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12795,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12795,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12795,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12795,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12795,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12795,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12795,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12795,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12795,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12795,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12795,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12795,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12795,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12795,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12795,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12795,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12795,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12795,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12795,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12795,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12795,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12795,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12795,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12795,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12795,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12795,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12795,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12795,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12795,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12795,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12795,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12795,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12795,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12795,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12795,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12795,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12795,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12795,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12795,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12795,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12795,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12795,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12795,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12795,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12795,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12795,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12795,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12795,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12795,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12795,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12795,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12795,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12795,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12795,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12795,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12795,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12795,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12795,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12795,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12795,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12795,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12795,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12795,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12795,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12795,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12795,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12795,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12795,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12795,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12795,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12795,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12795,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12795,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12795,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12795,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12795,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12795,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12795,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12795,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12795,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12795,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12795 : FrameRepair 12795 scalarRow12795 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12795Cells j).1 (repair12795Cells j).2.1
  endpoint_upper := fun j => ((repair12795Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12795Cells j).2.2

theorem repair12796Cells (j : Fin 43) :
    0 ≤ (scalarRow12796.table (sourceIndex j)).upper ∧
    (scalarRow12796.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12796.table (sourceIndex j)).centre) /
      (scalarRow12796.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12796.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12796,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12796,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12796,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12796,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12796,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12796,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12796,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12796,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12796,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12796,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12796,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12796,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12796,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12796,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12796,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12796,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12796,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12796,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12796,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12796,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12796,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12796,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12796,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12796,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12796,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12796,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12796,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12796,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12796,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12796,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12796,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12796,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12796,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12796,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12796,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12796,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12796,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12796,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12796,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12796,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12796,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12796,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12796,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12796,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12796,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12796,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12796,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12796,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12796,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12796,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12796,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12796,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12796,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12796,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12796,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12796,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12796,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12796,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12796,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12796,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12796,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12796,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12796,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12796,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12796,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12796,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12796,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12796,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12796,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12796,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12796,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12796,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12796,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12796,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12796,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12796,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12796,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12796,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12796,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12796,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12796,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12796,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12796,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12796,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12796,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12796,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12796 : FrameRepair 12796 scalarRow12796 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12796Cells j).1 (repair12796Cells j).2.1
  endpoint_upper := fun j => ((repair12796Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12796Cells j).2.2

theorem repair12797Cells (j : Fin 43) :
    0 ≤ (scalarRow12797.table (sourceIndex j)).upper ∧
    (scalarRow12797.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12797.table (sourceIndex j)).centre) /
      (scalarRow12797.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12797.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12797,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12797,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12797,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12797,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12797,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12797,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12797,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12797,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12797,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12797,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12797,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12797,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12797,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12797,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12797,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12797,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12797,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12797,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12797,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12797,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12797,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12797,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12797,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12797,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12797,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12797,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12797,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12797,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12797,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12797,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12797,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12797,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12797,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12797,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12797,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12797,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12797,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12797,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12797,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12797,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12797,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12797,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12797,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12797,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12797,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12797,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12797,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12797,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12797,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12797,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12797,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12797,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12797,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12797,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12797,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12797,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12797,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12797,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12797,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12797,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12797,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12797,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12797,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12797,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12797,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12797,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12797,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12797,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12797,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12797,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12797,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12797,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12797,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12797,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12797,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12797,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12797,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12797,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12797,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12797,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12797,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12797,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12797,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12797,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12797,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12797,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12797 : FrameRepair 12797 scalarRow12797 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12797Cells j).1 (repair12797Cells j).2.1
  endpoint_upper := fun j => ((repair12797Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12797Cells j).2.2

theorem repair12798Cells (j : Fin 43) :
    0 ≤ (scalarRow12798.table (sourceIndex j)).upper ∧
    (scalarRow12798.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12798.table (sourceIndex j)).centre) /
      (scalarRow12798.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12798.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12798,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12798,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12798,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12798,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12798,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12798,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12798,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12798,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12798,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12798,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12798,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12798,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12798,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12798,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12798,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12798,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12798,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12798,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12798,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12798,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12798,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12798,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12798,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12798,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12798,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12798,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12798,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12798,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12798,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12798,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12798,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12798,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12798,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12798,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12798,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12798,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12798,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12798,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12798,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12798,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12798,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12798,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12798,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12798,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12798,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12798,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12798,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12798,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12798,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12798,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12798,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12798,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12798,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12798,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12798,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12798,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12798,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12798,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12798,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12798,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12798,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12798,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12798,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12798,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12798,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12798,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12798,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12798,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12798,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12798,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12798,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12798,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12798,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12798,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12798,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12798,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12798,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12798,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12798,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12798,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12798,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12798,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12798,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12798,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12798,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12798,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12798 : FrameRepair 12798 scalarRow12798 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12798Cells j).1 (repair12798Cells j).2.1
  endpoint_upper := fun j => ((repair12798Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12798Cells j).2.2

theorem repair12799Cells (j : Fin 43) :
    0 ≤ (scalarRow12799.table (sourceIndex j)).upper ∧
    (scalarRow12799.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12799.table (sourceIndex j)).centre) /
      (scalarRow12799.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12799.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12799,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12799,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12799,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12799,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12799,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12799,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12799,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12799,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12799,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12799,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12799,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12799,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12799,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12799,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12799,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12799,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12799,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12799,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12799,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12799,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12799,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12799,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12799,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12799,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12799,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12799,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12799,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12799,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12799,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12799,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12799,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12799,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12799,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12799,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12799,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12799,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12799,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12799,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12799,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12799,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12799,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12799,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12799,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12799,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12799,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12799,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12799,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12799,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12799,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12799,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12799,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12799,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12799,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12799,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12799,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12799,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12799,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12799,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12799,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12799,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12799,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12799,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12799,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12799,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12799,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12799,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12799,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12799,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12799,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12799,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12799,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12799,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12799,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12799,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12799,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12799,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12799,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12799,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12799,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12799,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12799,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12799,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12799,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12799,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12799,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12799,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12799 : FrameRepair 12799 scalarRow12799 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12799Cells j).1 (repair12799Cells j).2.1
  endpoint_upper := fun j => ((repair12799Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12799Cells j).2.2

end BstLean.Part269
