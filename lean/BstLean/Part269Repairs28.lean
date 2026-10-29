import BstLean.Part269Rows28
import BstLean.Part269RepairCommon
namespace BstLean.Part269
open Real Set BstLean.Part255 BstLean.Part263 BstLean.Part264
theorem repair13050Cells (j : Fin 43) :
    0 ≤ (scalarRow13050.table (sourceIndex j)).upper ∧
    (scalarRow13050.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13050.table (sourceIndex j)).centre) /
      (scalarRow13050.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13050.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13050,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13050,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13050,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13050,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13050,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13050,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13050,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13050,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13050,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13050,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13050,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13050,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13050,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13050,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13050,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13050,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13050,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13050,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13050,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13050,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13050,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13050,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13050,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13050,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13050,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13050,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13050,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13050,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13050,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13050,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13050,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13050,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13050,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13050,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13050,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13050,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13050,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13050,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13050,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13050,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13050,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13050,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13050,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13050,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13050,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13050,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13050,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13050,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13050,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13050,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13050,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13050,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13050,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13050,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13050,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13050,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13050,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13050,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13050,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13050,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13050,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13050,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13050,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13050,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13050,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13050,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13050,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13050,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13050,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13050,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13050,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13050,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13050,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13050,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13050,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13050,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13050,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13050,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13050,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13050,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13050,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13050,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13050,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13050,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13050,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13050,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13050 : FrameRepair 13050 scalarRow13050 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13050Cells j).1 (repair13050Cells j).2.1
  endpoint_upper := fun j => ((repair13050Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13050Cells j).2.2

theorem repair13051Cells (j : Fin 43) :
    0 ≤ (scalarRow13051.table (sourceIndex j)).upper ∧
    (scalarRow13051.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13051.table (sourceIndex j)).centre) /
      (scalarRow13051.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13051.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13051,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13051,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13051,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13051,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13051,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13051,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13051,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13051,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13051,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13051,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13051,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13051,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13051,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13051,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13051,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13051,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13051,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13051,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13051,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13051,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13051,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13051,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13051,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13051,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13051,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13051,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13051,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13051,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13051,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13051,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13051,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13051,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13051,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13051,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13051,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13051,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13051,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13051,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13051,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13051,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13051,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13051,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13051,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13051,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13051,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13051,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13051,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13051,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13051,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13051,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13051,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13051,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13051,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13051,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13051,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13051,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13051,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13051,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13051,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13051,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13051,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13051,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13051,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13051,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13051,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13051,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13051,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13051,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13051,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13051,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13051,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13051,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13051,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13051,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13051,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13051,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13051,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13051,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13051,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13051,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13051,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13051,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13051,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13051,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13051,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13051,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13051 : FrameRepair 13051 scalarRow13051 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13051Cells j).1 (repair13051Cells j).2.1
  endpoint_upper := fun j => ((repair13051Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13051Cells j).2.2

theorem repair13052Cells (j : Fin 43) :
    0 ≤ (scalarRow13052.table (sourceIndex j)).upper ∧
    (scalarRow13052.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13052.table (sourceIndex j)).centre) /
      (scalarRow13052.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13052.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13052,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13052,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13052,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13052,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13052,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13052,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13052,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13052,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13052,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13052,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13052,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13052,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13052,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13052,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13052,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13052,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13052,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13052,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13052,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13052,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13052,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13052,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13052,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13052,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13052,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13052,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13052,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13052,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13052,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13052,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13052,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13052,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13052,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13052,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13052,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13052,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13052,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13052,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13052,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13052,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13052,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13052,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13052,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13052,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13052,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13052,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13052,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13052,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13052,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13052,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13052,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13052,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13052,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13052,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13052,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13052,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13052,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13052,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13052,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13052,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13052,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13052,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13052,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13052,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13052,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13052,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13052,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13052,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13052,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13052,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13052,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13052,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13052,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13052,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13052,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13052,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13052,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13052,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13052,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13052,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13052,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13052,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13052,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13052,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13052,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13052,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13052 : FrameRepair 13052 scalarRow13052 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13052Cells j).1 (repair13052Cells j).2.1
  endpoint_upper := fun j => ((repair13052Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13052Cells j).2.2

theorem repair13053Cells (j : Fin 43) :
    0 ≤ (scalarRow13053.table (sourceIndex j)).upper ∧
    (scalarRow13053.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13053.table (sourceIndex j)).centre) /
      (scalarRow13053.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13053.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13053,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13053,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13053,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13053,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13053,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13053,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13053,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13053,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13053,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13053,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13053,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13053,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13053,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13053,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13053,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13053,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13053,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13053,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13053,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13053,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13053,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13053,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13053,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13053,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13053,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13053,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13053,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13053,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13053,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13053,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13053,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13053,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13053,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13053,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13053,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13053,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13053,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13053,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13053,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13053,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13053,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13053,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13053,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13053,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13053,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13053,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13053,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13053,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13053,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13053,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13053,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13053,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13053,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13053,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13053,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13053,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13053,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13053,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13053,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13053,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13053,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13053,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13053,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13053,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13053,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13053,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13053,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13053,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13053,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13053,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13053,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13053,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13053,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13053,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13053,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13053,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13053,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13053,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13053,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13053,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13053,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13053,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13053,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13053,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13053,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13053,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13053 : FrameRepair 13053 scalarRow13053 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13053Cells j).1 (repair13053Cells j).2.1
  endpoint_upper := fun j => ((repair13053Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13053Cells j).2.2

theorem repair13054Cells (j : Fin 43) :
    0 ≤ (scalarRow13054.table (sourceIndex j)).upper ∧
    (scalarRow13054.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13054.table (sourceIndex j)).centre) /
      (scalarRow13054.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13054.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13054,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13054,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13054,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13054,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13054,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13054,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13054,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13054,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13054,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13054,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13054,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13054,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13054,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13054,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13054,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13054,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13054,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13054,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13054,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13054,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13054,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13054,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13054,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13054,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13054,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13054,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13054,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13054,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13054,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13054,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13054,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13054,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13054,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13054,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13054,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13054,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13054,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13054,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13054,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13054,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13054,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13054,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13054,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13054,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13054,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13054,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13054,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13054,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13054,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13054,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13054,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13054,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13054,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13054,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13054,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13054,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13054,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13054,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13054,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13054,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13054,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13054,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13054,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13054,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13054,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13054,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13054,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13054,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13054,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13054,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13054,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13054,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13054,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13054,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13054,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13054,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13054,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13054,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13054,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13054,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13054,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13054,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13054,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13054,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13054,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13054,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13054 : FrameRepair 13054 scalarRow13054 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13054Cells j).1 (repair13054Cells j).2.1
  endpoint_upper := fun j => ((repair13054Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13054Cells j).2.2

theorem repair13055Cells (j : Fin 43) :
    0 ≤ (scalarRow13055.table (sourceIndex j)).upper ∧
    (scalarRow13055.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13055.table (sourceIndex j)).centre) /
      (scalarRow13055.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13055.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13055,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13055,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13055,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13055,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13055,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13055,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13055,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13055,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13055,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13055,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13055,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13055,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13055,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13055,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13055,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13055,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13055,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13055,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13055,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13055,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13055,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13055,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13055,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13055,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13055,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13055,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13055,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13055,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13055,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13055,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13055,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13055,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13055,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13055,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13055,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13055,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13055,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13055,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13055,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13055,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13055,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13055,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13055,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13055,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13055,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13055,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13055,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13055,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13055,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13055,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13055,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13055,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13055,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13055,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13055,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13055,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13055,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13055,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13055,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13055,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13055,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13055,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13055,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13055,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13055,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13055,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13055,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13055,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13055,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13055,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13055,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13055,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13055,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13055,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13055,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13055,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13055,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13055,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13055,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13055,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13055,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13055,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13055,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13055,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13055,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13055,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13055 : FrameRepair 13055 scalarRow13055 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13055Cells j).1 (repair13055Cells j).2.1
  endpoint_upper := fun j => ((repair13055Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13055Cells j).2.2

theorem repair13056Cells (j : Fin 43) :
    0 ≤ (scalarRow13056.table (sourceIndex j)).upper ∧
    (scalarRow13056.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13056.table (sourceIndex j)).centre) /
      (scalarRow13056.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13056.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13056,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13056,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13056,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13056,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13056,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13056,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13056,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13056,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13056,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13056,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13056,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13056,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13056,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13056,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13056,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13056,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13056,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13056,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13056,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13056,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13056,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13056,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13056,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13056,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13056,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13056,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13056,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13056,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13056,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13056,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13056,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13056,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13056,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13056,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13056,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13056,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13056,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13056,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13056,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13056,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13056,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13056,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13056,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13056,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13056,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13056,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13056,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13056,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13056,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13056,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13056,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13056,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13056,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13056,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13056,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13056,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13056,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13056,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13056,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13056,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13056,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13056,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13056,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13056,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13056,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13056,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13056,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13056,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13056,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13056,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13056,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13056,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13056,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13056,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13056,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13056,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13056,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13056,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13056,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13056,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13056,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13056,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13056,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13056,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13056,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13056,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13056 : FrameRepair 13056 scalarRow13056 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13056Cells j).1 (repair13056Cells j).2.1
  endpoint_upper := fun j => ((repair13056Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13056Cells j).2.2

theorem repair13057Cells (j : Fin 43) :
    0 ≤ (scalarRow13057.table (sourceIndex j)).upper ∧
    (scalarRow13057.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13057.table (sourceIndex j)).centre) /
      (scalarRow13057.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13057.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13057,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13057,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13057,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13057,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13057,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13057,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13057,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13057,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13057,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13057,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13057,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13057,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13057,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13057,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13057,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13057,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13057,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13057,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13057,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13057,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13057,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13057,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13057,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13057,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13057,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13057,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13057,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13057,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13057,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13057,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13057,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13057,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13057,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13057,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13057,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13057,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13057,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13057,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13057,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13057,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13057,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13057,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13057,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13057,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13057,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13057,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13057,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13057,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13057,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13057,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13057,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13057,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13057,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13057,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13057,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13057,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13057,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13057,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13057,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13057,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13057,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13057,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13057,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13057,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13057,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13057,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13057,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13057,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13057,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13057,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13057,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13057,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13057,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13057,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13057,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13057,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13057,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13057,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13057,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13057,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13057,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13057,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13057,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13057,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13057,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13057,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13057 : FrameRepair 13057 scalarRow13057 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13057Cells j).1 (repair13057Cells j).2.1
  endpoint_upper := fun j => ((repair13057Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13057Cells j).2.2

theorem repair13058Cells (j : Fin 43) :
    0 ≤ (scalarRow13058.table (sourceIndex j)).upper ∧
    (scalarRow13058.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13058.table (sourceIndex j)).centre) /
      (scalarRow13058.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13058.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13058,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13058,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13058,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13058,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13058,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13058,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13058,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13058,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13058,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13058,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13058,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13058,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13058,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13058,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13058,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13058,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13058,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13058,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13058,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13058,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13058,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13058,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13058,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13058,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13058,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13058,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13058,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13058,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13058,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13058,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13058,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13058,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13058,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13058,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13058,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13058,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13058,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13058,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13058,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13058,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13058,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13058,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13058,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13058,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13058,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13058,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13058,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13058,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13058,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13058,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13058,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13058,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13058,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13058,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13058,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13058,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13058,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13058,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13058,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13058,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13058,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13058,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13058,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13058,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13058,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13058,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13058,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13058,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13058,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13058,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13058,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13058,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13058,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13058,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13058,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13058,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13058,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13058,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13058,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13058,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13058,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13058,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13058,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13058,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13058,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13058,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13058 : FrameRepair 13058 scalarRow13058 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13058Cells j).1 (repair13058Cells j).2.1
  endpoint_upper := fun j => ((repair13058Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13058Cells j).2.2

theorem repair13059Cells (j : Fin 43) :
    0 ≤ (scalarRow13059.table (sourceIndex j)).upper ∧
    (scalarRow13059.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13059.table (sourceIndex j)).centre) /
      (scalarRow13059.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13059.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13059,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13059,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13059,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13059,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13059,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13059,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13059,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13059,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13059,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13059,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13059,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13059,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13059,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13059,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13059,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13059,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13059,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13059,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13059,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13059,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13059,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13059,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13059,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13059,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13059,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13059,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13059,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13059,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13059,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13059,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13059,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13059,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13059,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13059,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13059,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13059,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13059,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13059,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13059,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13059,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13059,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13059,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13059,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13059,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13059,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13059,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13059,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13059,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13059,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13059,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13059,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13059,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13059,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13059,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13059,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13059,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13059,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13059,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13059,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13059,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13059,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13059,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13059,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13059,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13059,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13059,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13059,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13059,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13059,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13059,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13059,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13059,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13059,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13059,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13059,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13059,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13059,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13059,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13059,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13059,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13059,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13059,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13059,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13059,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13059,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13059,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13059 : FrameRepair 13059 scalarRow13059 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13059Cells j).1 (repair13059Cells j).2.1
  endpoint_upper := fun j => ((repair13059Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13059Cells j).2.2

theorem repair13060Cells (j : Fin 43) :
    0 ≤ (scalarRow13060.table (sourceIndex j)).upper ∧
    (scalarRow13060.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13060.table (sourceIndex j)).centre) /
      (scalarRow13060.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13060.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13060,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13060,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13060,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13060,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13060,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13060,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13060,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13060,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13060,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13060,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13060,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13060,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13060,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13060,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13060,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13060,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13060,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13060,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13060,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13060,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13060,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13060,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13060,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13060,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13060,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13060,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13060,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13060,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13060,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13060,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13060,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13060,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13060,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13060,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13060,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13060,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13060,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13060,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13060,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13060,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13060,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13060,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13060,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13060,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13060,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13060,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13060,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13060,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13060,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13060,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13060,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13060,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13060,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13060,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13060,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13060,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13060,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13060,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13060,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13060,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13060,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13060,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13060,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13060,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13060,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13060,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13060,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13060,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13060,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13060,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13060,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13060,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13060,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13060,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13060,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13060,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13060,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13060,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13060,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13060,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13060,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13060,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13060,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13060,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13060,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13060,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13060 : FrameRepair 13060 scalarRow13060 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13060Cells j).1 (repair13060Cells j).2.1
  endpoint_upper := fun j => ((repair13060Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13060Cells j).2.2

theorem repair13061Cells (j : Fin 43) :
    0 ≤ (scalarRow13061.table (sourceIndex j)).upper ∧
    (scalarRow13061.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13061.table (sourceIndex j)).centre) /
      (scalarRow13061.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13061.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13061,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13061,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13061,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13061,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13061,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13061,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13061,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13061,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13061,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13061,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13061,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13061,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13061,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13061,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13061,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13061,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13061,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13061,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13061,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13061,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13061,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13061,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13061,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13061,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13061,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13061,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13061,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13061,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13061,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13061,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13061,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13061,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13061,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13061,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13061,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13061,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13061,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13061,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13061,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13061,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13061,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13061,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13061,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13061,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13061,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13061,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13061,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13061,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13061,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13061,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13061,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13061,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13061,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13061,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13061,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13061,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13061,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13061,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13061,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13061,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13061,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13061,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13061,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13061,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13061,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13061,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13061,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13061,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13061,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13061,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13061,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13061,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13061,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13061,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13061,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13061,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13061,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13061,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13061,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13061,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13061,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13061,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13061,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13061,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13061,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13061,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13061 : FrameRepair 13061 scalarRow13061 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13061Cells j).1 (repair13061Cells j).2.1
  endpoint_upper := fun j => ((repair13061Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13061Cells j).2.2

theorem repair13062Cells (j : Fin 43) :
    0 ≤ (scalarRow13062.table (sourceIndex j)).upper ∧
    (scalarRow13062.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13062.table (sourceIndex j)).centre) /
      (scalarRow13062.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13062.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13062,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13062,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13062,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13062,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13062,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13062,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13062,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13062,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13062,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13062,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13062,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13062,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13062,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13062,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13062,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13062,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13062,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13062,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13062,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13062,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13062,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13062,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13062,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13062,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13062,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13062,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13062,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13062,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13062,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13062,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13062,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13062,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13062,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13062,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13062,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13062,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13062,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13062,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13062,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13062,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13062,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13062,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13062,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13062,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13062,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13062,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13062,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13062,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13062,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13062,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13062,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13062,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13062,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13062,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13062,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13062,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13062,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13062,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13062,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13062,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13062,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13062,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13062,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13062,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13062,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13062,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13062,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13062,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13062,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13062,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13062,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13062,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13062,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13062,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13062,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13062,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13062,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13062,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13062,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13062,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13062,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13062,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13062,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13062,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13062,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13062,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13062 : FrameRepair 13062 scalarRow13062 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13062Cells j).1 (repair13062Cells j).2.1
  endpoint_upper := fun j => ((repair13062Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13062Cells j).2.2

theorem repair13063Cells (j : Fin 43) :
    0 ≤ (scalarRow13063.table (sourceIndex j)).upper ∧
    (scalarRow13063.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13063.table (sourceIndex j)).centre) /
      (scalarRow13063.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13063.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13063,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13063,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13063,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13063,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13063,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13063,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13063,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13063,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13063,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13063,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13063,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13063,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13063,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13063,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13063,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13063,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13063,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13063,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13063,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13063,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13063,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13063,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13063,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13063,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13063,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13063,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13063,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13063,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13063,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13063,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13063,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13063,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13063,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13063,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13063,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13063,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13063,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13063,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13063,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13063,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13063,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13063,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13063,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13063,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13063,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13063,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13063,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13063,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13063,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13063,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13063,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13063,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13063,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13063,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13063,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13063,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13063,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13063,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13063,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13063,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13063,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13063,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13063,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13063,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13063,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13063,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13063,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13063,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13063,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13063,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13063,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13063,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13063,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13063,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13063,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13063,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13063,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13063,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13063,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13063,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13063,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13063,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13063,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13063,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13063,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13063,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13063 : FrameRepair 13063 scalarRow13063 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13063Cells j).1 (repair13063Cells j).2.1
  endpoint_upper := fun j => ((repair13063Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13063Cells j).2.2

theorem repair13064Cells (j : Fin 43) :
    0 ≤ (scalarRow13064.table (sourceIndex j)).upper ∧
    (scalarRow13064.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13064.table (sourceIndex j)).centre) /
      (scalarRow13064.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13064.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13064,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13064,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13064,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13064,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13064,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13064,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13064,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13064,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13064,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13064,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13064,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13064,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13064,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13064,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13064,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13064,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13064,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13064,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13064,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13064,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13064,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13064,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13064,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13064,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13064,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13064,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13064,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13064,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13064,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13064,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13064,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13064,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13064,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13064,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13064,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13064,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13064,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13064,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13064,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13064,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13064,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13064,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13064,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13064,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13064,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13064,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13064,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13064,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13064,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13064,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13064,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13064,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13064,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13064,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13064,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13064,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13064,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13064,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13064,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13064,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13064,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13064,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13064,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13064,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13064,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13064,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13064,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13064,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13064,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13064,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13064,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13064,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13064,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13064,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13064,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13064,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13064,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13064,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13064,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13064,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13064,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13064,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13064,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13064,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13064,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13064,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13064 : FrameRepair 13064 scalarRow13064 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13064Cells j).1 (repair13064Cells j).2.1
  endpoint_upper := fun j => ((repair13064Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13064Cells j).2.2

theorem repair13065Cells (j : Fin 43) :
    0 ≤ (scalarRow13065.table (sourceIndex j)).upper ∧
    (scalarRow13065.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13065.table (sourceIndex j)).centre) /
      (scalarRow13065.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13065.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13065,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13065,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13065,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13065,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13065,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13065,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13065,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13065,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13065,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13065,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13065,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13065,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13065,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13065,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13065,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13065,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13065,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13065,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13065,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13065,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13065,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13065,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13065,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13065,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13065,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13065,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13065,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13065,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13065,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13065,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13065,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13065,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13065,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13065,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13065,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13065,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13065,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13065,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13065,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13065,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13065,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13065,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13065,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13065,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13065,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13065,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13065,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13065,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13065,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13065,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13065,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13065,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13065,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13065,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13065,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13065,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13065,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13065,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13065,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13065,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13065,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13065,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13065,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13065,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13065,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13065,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13065,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13065,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13065,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13065,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13065,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13065,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13065,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13065,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13065,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13065,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13065,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13065,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13065,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13065,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13065,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13065,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13065,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13065,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13065,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13065,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13065 : FrameRepair 13065 scalarRow13065 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13065Cells j).1 (repair13065Cells j).2.1
  endpoint_upper := fun j => ((repair13065Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13065Cells j).2.2

theorem repair13066Cells (j : Fin 43) :
    0 ≤ (scalarRow13066.table (sourceIndex j)).upper ∧
    (scalarRow13066.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13066.table (sourceIndex j)).centre) /
      (scalarRow13066.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13066.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13066,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13066,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13066,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13066,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13066,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13066,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13066,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13066,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13066,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13066,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13066,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13066,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13066,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13066,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13066,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13066,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13066,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13066,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13066,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13066,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13066,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13066,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13066,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13066,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13066,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13066,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13066,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13066,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13066,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13066,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13066,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13066,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13066,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13066,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13066,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13066,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13066,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13066,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13066,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13066,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13066,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13066,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13066,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13066,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13066,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13066,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13066,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13066,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13066,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13066,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13066,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13066,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13066,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13066,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13066,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13066,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13066,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13066,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13066,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13066,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13066,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13066,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13066,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13066,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13066,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13066,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13066,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13066,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13066,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13066,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13066,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13066,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13066,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13066,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13066,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13066,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13066,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13066,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13066,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13066,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13066,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13066,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13066,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13066,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13066,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13066,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13066 : FrameRepair 13066 scalarRow13066 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13066Cells j).1 (repair13066Cells j).2.1
  endpoint_upper := fun j => ((repair13066Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13066Cells j).2.2

theorem repair13067Cells (j : Fin 43) :
    0 ≤ (scalarRow13067.table (sourceIndex j)).upper ∧
    (scalarRow13067.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13067.table (sourceIndex j)).centre) /
      (scalarRow13067.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13067.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13067,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13067,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13067,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13067,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13067,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13067,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13067,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13067,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13067,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13067,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13067,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13067,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13067,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13067,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13067,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13067,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13067,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13067,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13067,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13067,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13067,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13067,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13067,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13067,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13067,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13067,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13067,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13067,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13067,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13067,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13067,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13067,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13067,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13067,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13067,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13067,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13067,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13067,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13067,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13067,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13067,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13067,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13067,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13067,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13067,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13067,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13067,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13067,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13067,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13067,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13067,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13067,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13067,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13067,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13067,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13067,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13067,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13067,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13067,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13067,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13067,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13067,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13067,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13067,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13067,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13067,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13067,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13067,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13067,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13067,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13067,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13067,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13067,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13067,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13067,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13067,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13067,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13067,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13067,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13067,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13067,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13067,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13067,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13067,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13067,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13067,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13067 : FrameRepair 13067 scalarRow13067 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13067Cells j).1 (repair13067Cells j).2.1
  endpoint_upper := fun j => ((repair13067Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13067Cells j).2.2

theorem repair13068Cells (j : Fin 43) :
    0 ≤ (scalarRow13068.table (sourceIndex j)).upper ∧
    (scalarRow13068.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13068.table (sourceIndex j)).centre) /
      (scalarRow13068.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13068.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13068,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13068,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13068,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13068,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13068,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13068,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13068,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13068,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13068,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13068,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13068,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13068,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13068,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13068,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13068,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13068,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13068,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13068,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13068,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13068,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13068,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13068,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13068,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13068,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13068,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13068,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13068,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13068,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13068,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13068,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13068,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13068,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13068,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13068,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13068,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13068,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13068,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13068,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13068,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13068,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13068,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13068,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13068,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13068,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13068,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13068,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13068,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13068,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13068,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13068,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13068,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13068,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13068,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13068,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13068,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13068,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13068,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13068,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13068,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13068,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13068,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13068,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13068,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13068,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13068,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13068,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13068,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13068,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13068,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13068,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13068,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13068,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13068,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13068,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13068,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13068,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13068,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13068,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13068,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13068,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13068,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13068,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13068,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13068,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13068,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13068,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13068 : FrameRepair 13068 scalarRow13068 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13068Cells j).1 (repair13068Cells j).2.1
  endpoint_upper := fun j => ((repair13068Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13068Cells j).2.2

theorem repair13069Cells (j : Fin 43) :
    0 ≤ (scalarRow13069.table (sourceIndex j)).upper ∧
    (scalarRow13069.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13069.table (sourceIndex j)).centre) /
      (scalarRow13069.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13069.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13069,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13069,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13069,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13069,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13069,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13069,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13069,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13069,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13069,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13069,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13069,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13069,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13069,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13069,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13069,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13069,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13069,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13069,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13069,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13069,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13069,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13069,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13069,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13069,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13069,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13069,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13069,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13069,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13069,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13069,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13069,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13069,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13069,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13069,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13069,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13069,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13069,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13069,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13069,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13069,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13069,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13069,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13069,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13069,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13069,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13069,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13069,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13069,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13069,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13069,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13069,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13069,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13069,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13069,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13069,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13069,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13069,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13069,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13069,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13069,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13069,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13069,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13069,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13069,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13069,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13069,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13069,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13069,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13069,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13069,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13069,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13069,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13069,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13069,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13069,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13069,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13069,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13069,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13069,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13069,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13069,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13069,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13069,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13069,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13069,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13069,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13069 : FrameRepair 13069 scalarRow13069 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13069Cells j).1 (repair13069Cells j).2.1
  endpoint_upper := fun j => ((repair13069Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13069Cells j).2.2

theorem repair13070Cells (j : Fin 43) :
    0 ≤ (scalarRow13070.table (sourceIndex j)).upper ∧
    (scalarRow13070.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13070.table (sourceIndex j)).centre) /
      (scalarRow13070.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13070.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13070,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13070,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13070,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13070,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13070,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13070,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13070,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13070,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13070,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13070,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13070,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13070,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13070,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13070,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13070,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13070,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13070,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13070,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13070,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13070,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13070,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13070,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13070,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13070,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13070,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13070,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13070,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13070,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13070,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13070,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13070,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13070,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13070,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13070,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13070,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13070,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13070,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13070,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13070,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13070,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13070,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13070,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13070,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13070,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13070,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13070,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13070,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13070,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13070,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13070,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13070,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13070,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13070,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13070,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13070,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13070,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13070,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13070,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13070,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13070,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13070,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13070,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13070,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13070,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13070,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13070,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13070,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13070,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13070,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13070,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13070,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13070,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13070,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13070,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13070,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13070,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13070,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13070,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13070,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13070,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13070,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13070,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13070,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13070,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13070,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13070,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13070 : FrameRepair 13070 scalarRow13070 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13070Cells j).1 (repair13070Cells j).2.1
  endpoint_upper := fun j => ((repair13070Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13070Cells j).2.2

theorem repair13071Cells (j : Fin 43) :
    0 ≤ (scalarRow13071.table (sourceIndex j)).upper ∧
    (scalarRow13071.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13071.table (sourceIndex j)).centre) /
      (scalarRow13071.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13071.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13071,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13071,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13071,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13071,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13071,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13071,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13071,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13071,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13071,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13071,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13071,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13071,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13071,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13071,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13071,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13071,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13071,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13071,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13071,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13071,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13071,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13071,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13071,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13071,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13071,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13071,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13071,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13071,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13071,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13071,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13071,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13071,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13071,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13071,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13071,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13071,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13071,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13071,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13071,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13071,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13071,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13071,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13071,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13071,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13071,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13071,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13071,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13071,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13071,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13071,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13071,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13071,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13071,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13071,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13071,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13071,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13071,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13071,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13071,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13071,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13071,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13071,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13071,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13071,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13071,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13071,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13071,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13071,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13071,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13071,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13071,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13071,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13071,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13071,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13071,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13071,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13071,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13071,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13071,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13071,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13071,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13071,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13071,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13071,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13071,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13071,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13071 : FrameRepair 13071 scalarRow13071 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13071Cells j).1 (repair13071Cells j).2.1
  endpoint_upper := fun j => ((repair13071Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13071Cells j).2.2

theorem repair13072Cells (j : Fin 43) :
    0 ≤ (scalarRow13072.table (sourceIndex j)).upper ∧
    (scalarRow13072.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13072.table (sourceIndex j)).centre) /
      (scalarRow13072.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13072.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13072,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13072,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13072,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13072,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13072,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13072,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13072,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13072,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13072,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13072,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13072,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13072,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13072,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13072,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13072,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13072,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13072,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13072,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13072,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13072,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13072,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13072,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13072,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13072,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13072,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13072,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13072,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13072,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13072,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13072,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13072,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13072,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13072,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13072,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13072,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13072,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13072,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13072,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13072,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13072,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13072,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13072,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13072,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13072,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13072,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13072,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13072,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13072,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13072,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13072,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13072,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13072,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13072,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13072,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13072,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13072,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13072,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13072,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13072,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13072,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13072,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13072,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13072,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13072,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13072,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13072,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13072,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13072,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13072,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13072,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13072,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13072,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13072,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13072,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13072,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13072,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13072,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13072,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13072,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13072,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13072,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13072,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13072,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13072,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13072,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13072,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13072 : FrameRepair 13072 scalarRow13072 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13072Cells j).1 (repair13072Cells j).2.1
  endpoint_upper := fun j => ((repair13072Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13072Cells j).2.2

theorem repair13073Cells (j : Fin 43) :
    0 ≤ (scalarRow13073.table (sourceIndex j)).upper ∧
    (scalarRow13073.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13073.table (sourceIndex j)).centre) /
      (scalarRow13073.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13073.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13073,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13073,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13073,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13073,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13073,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13073,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13073,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13073,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13073,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13073,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13073,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13073,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13073,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13073,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13073,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13073,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13073,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13073,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13073,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13073,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13073,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13073,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13073,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13073,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13073,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13073,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13073,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13073,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13073,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13073,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13073,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13073,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13073,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13073,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13073,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13073,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13073,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13073,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13073,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13073,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13073,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13073,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13073,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13073,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13073,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13073,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13073,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13073,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13073,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13073,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13073,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13073,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13073,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13073,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13073,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13073,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13073,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13073,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13073,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13073,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13073,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13073,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13073,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13073,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13073,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13073,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13073,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13073,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13073,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13073,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13073,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13073,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13073,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13073,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13073,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13073,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13073,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13073,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13073,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13073,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13073,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13073,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13073,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13073,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13073,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13073,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13073 : FrameRepair 13073 scalarRow13073 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13073Cells j).1 (repair13073Cells j).2.1
  endpoint_upper := fun j => ((repair13073Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13073Cells j).2.2

theorem repair13074Cells (j : Fin 43) :
    0 ≤ (scalarRow13074.table (sourceIndex j)).upper ∧
    (scalarRow13074.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13074.table (sourceIndex j)).centre) /
      (scalarRow13074.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13074.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13074,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13074,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13074,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13074,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13074,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13074,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13074,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13074,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13074,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13074,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13074,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13074,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13074,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13074,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13074,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13074,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13074,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13074,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13074,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13074,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13074,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13074,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13074,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13074,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13074,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13074,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13074,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13074,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13074,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13074,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13074,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13074,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13074,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13074,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13074,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13074,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13074,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13074,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13074,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13074,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13074,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13074,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13074,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13074,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13074,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13074,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13074,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13074,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13074,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13074,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13074,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13074,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13074,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13074,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13074,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13074,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13074,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13074,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13074,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13074,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13074,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13074,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13074,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13074,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13074,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13074,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13074,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13074,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13074,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13074,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13074,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13074,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13074,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13074,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13074,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13074,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13074,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13074,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13074,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13074,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13074,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13074,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13074,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13074,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13074,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13074,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13074 : FrameRepair 13074 scalarRow13074 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13074Cells j).1 (repair13074Cells j).2.1
  endpoint_upper := fun j => ((repair13074Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13074Cells j).2.2

end BstLean.Part269
