import BstLean.Part269Rows34
import BstLean.Part269RepairCommon
import BstLean.Part269Repair13224
namespace BstLean.Part269
open Real Set BstLean.Part255 BstLean.Part263 BstLean.Part264
theorem repair13200Cells (j : Fin 43) :
    0 ≤ (scalarRow13200.table (sourceIndex j)).upper ∧
    (scalarRow13200.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13200.table (sourceIndex j)).centre) /
      (scalarRow13200.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13200.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13200,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13200,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13200,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13200,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13200,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13200,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13200,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13200,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13200,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13200,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13200,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13200,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13200,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13200,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13200,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13200,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13200,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13200,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13200,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13200,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13200,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13200,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13200,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13200,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13200,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13200,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13200,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13200,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13200,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13200,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13200,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13200,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13200,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13200,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13200,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13200,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13200,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13200,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13200,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13200,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13200,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13200,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13200,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13200,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13200,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13200,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13200,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13200,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13200,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13200,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13200,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13200,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13200,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13200,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13200,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13200,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13200,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13200,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13200,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13200,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13200,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13200,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13200,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13200,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13200,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13200,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13200,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13200,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13200,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13200,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13200,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13200,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13200,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13200,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13200,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13200,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13200,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13200,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13200,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13200,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13200,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13200,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13200,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13200,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13200,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13200,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13200 : FrameRepair 13200 scalarRow13200 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13200Cells j).1 (repair13200Cells j).2.1
  endpoint_upper := fun j => ((repair13200Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13200Cells j).2.2

theorem repair13201Cells (j : Fin 43) :
    0 ≤ (scalarRow13201.table (sourceIndex j)).upper ∧
    (scalarRow13201.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13201.table (sourceIndex j)).centre) /
      (scalarRow13201.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13201.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13201,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13201,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13201,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13201,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13201,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13201,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13201,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13201,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13201,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13201,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13201,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13201,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13201,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13201,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13201,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13201,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13201,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13201,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13201,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13201,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13201,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13201,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13201,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13201,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13201,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13201,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13201,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13201,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13201,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13201,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13201,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13201,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13201,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13201,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13201,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13201,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13201,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13201,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13201,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13201,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13201,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13201,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13201,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13201,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13201,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13201,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13201,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13201,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13201,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13201,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13201,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13201,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13201,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13201,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13201,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13201,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13201,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13201,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13201,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13201,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13201,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13201,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13201,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13201,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13201,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13201,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13201,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13201,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13201,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13201,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13201,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13201,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13201,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13201,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13201,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13201,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13201,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13201,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13201,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13201,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13201,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13201,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13201,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13201,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13201,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13201,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13201 : FrameRepair 13201 scalarRow13201 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13201Cells j).1 (repair13201Cells j).2.1
  endpoint_upper := fun j => ((repair13201Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13201Cells j).2.2

theorem repair13202Cells (j : Fin 43) :
    0 ≤ (scalarRow13202.table (sourceIndex j)).upper ∧
    (scalarRow13202.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13202.table (sourceIndex j)).centre) /
      (scalarRow13202.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13202.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13202,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13202,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13202,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13202,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13202,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13202,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13202,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13202,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13202,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13202,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13202,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13202,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13202,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13202,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13202,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13202,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13202,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13202,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13202,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13202,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13202,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13202,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13202,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13202,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13202,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13202,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13202,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13202,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13202,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13202,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13202,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13202,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13202,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13202,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13202,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13202,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13202,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13202,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13202,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13202,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13202,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13202,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13202,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13202,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13202,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13202,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13202,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13202,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13202,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13202,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13202,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13202,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13202,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13202,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13202,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13202,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13202,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13202,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13202,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13202,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13202,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13202,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13202,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13202,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13202,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13202,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13202,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13202,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13202,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13202,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13202,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13202,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13202,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13202,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13202,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13202,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13202,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13202,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13202,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13202,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13202,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13202,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13202,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13202,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13202,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13202,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13202 : FrameRepair 13202 scalarRow13202 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13202Cells j).1 (repair13202Cells j).2.1
  endpoint_upper := fun j => ((repair13202Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13202Cells j).2.2

theorem repair13203Cells (j : Fin 43) :
    0 ≤ (scalarRow13203.table (sourceIndex j)).upper ∧
    (scalarRow13203.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13203.table (sourceIndex j)).centre) /
      (scalarRow13203.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13203.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13203,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13203,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13203,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13203,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13203,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13203,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13203,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13203,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13203,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13203,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13203,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13203,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13203,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13203,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13203,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13203,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13203,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13203,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13203,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13203,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13203,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13203,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13203,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13203,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13203,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13203,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13203,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13203,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13203,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13203,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13203,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13203,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13203,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13203,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13203,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13203,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13203,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13203,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13203,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13203,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13203,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13203,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13203,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13203,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13203,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13203,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13203,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13203,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13203,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13203,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13203,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13203,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13203,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13203,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13203,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13203,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13203,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13203,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13203,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13203,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13203,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13203,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13203,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13203,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13203,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13203,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13203,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13203,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13203,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13203,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13203,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13203,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13203,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13203,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13203,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13203,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13203,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13203,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13203,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13203,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13203,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13203,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13203,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13203,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13203,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13203,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13203 : FrameRepair 13203 scalarRow13203 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13203Cells j).1 (repair13203Cells j).2.1
  endpoint_upper := fun j => ((repair13203Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13203Cells j).2.2

theorem repair13204Cells (j : Fin 43) :
    0 ≤ (scalarRow13204.table (sourceIndex j)).upper ∧
    (scalarRow13204.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13204.table (sourceIndex j)).centre) /
      (scalarRow13204.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13204.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13204,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13204,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13204,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13204,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13204,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13204,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13204,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13204,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13204,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13204,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13204,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13204,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13204,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13204,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13204,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13204,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13204,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13204,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13204,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13204,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13204,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13204,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13204,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13204,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13204,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13204,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13204,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13204,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13204,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13204,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13204,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13204,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13204,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13204,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13204,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13204,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13204,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13204,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13204,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13204,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13204,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13204,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13204,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13204,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13204,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13204,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13204,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13204,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13204,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13204,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13204,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13204,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13204,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13204,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13204,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13204,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13204,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13204,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13204,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13204,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13204,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13204,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13204,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13204,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13204,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13204,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13204,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13204,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13204,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13204,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13204,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13204,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13204,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13204,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13204,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13204,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13204,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13204,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13204,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13204,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13204,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13204,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13204,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13204,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13204,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13204,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13204 : FrameRepair 13204 scalarRow13204 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13204Cells j).1 (repair13204Cells j).2.1
  endpoint_upper := fun j => ((repair13204Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13204Cells j).2.2

theorem repair13205Cells (j : Fin 43) :
    0 ≤ (scalarRow13205.table (sourceIndex j)).upper ∧
    (scalarRow13205.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13205.table (sourceIndex j)).centre) /
      (scalarRow13205.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13205.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13205,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13205,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13205,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13205,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13205,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13205,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13205,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13205,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13205,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13205,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13205,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13205,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13205,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13205,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13205,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13205,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13205,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13205,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13205,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13205,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13205,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13205,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13205,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13205,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13205,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13205,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13205,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13205,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13205,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13205,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13205,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13205,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13205,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13205,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13205,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13205,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13205,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13205,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13205,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13205,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13205,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13205,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13205,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13205,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13205,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13205,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13205,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13205,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13205,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13205,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13205,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13205,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13205,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13205,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13205,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13205,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13205,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13205,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13205,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13205,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13205,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13205,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13205,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13205,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13205,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13205,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13205,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13205,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13205,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13205,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13205,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13205,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13205,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13205,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13205,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13205,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13205,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13205,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13205,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13205,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13205,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13205,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13205,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13205,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13205,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13205,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13205 : FrameRepair 13205 scalarRow13205 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13205Cells j).1 (repair13205Cells j).2.1
  endpoint_upper := fun j => ((repair13205Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13205Cells j).2.2

theorem repair13206Cells (j : Fin 43) :
    0 ≤ (scalarRow13206.table (sourceIndex j)).upper ∧
    (scalarRow13206.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13206.table (sourceIndex j)).centre) /
      (scalarRow13206.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13206.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13206,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13206,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13206,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13206,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13206,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13206,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13206,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13206,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13206,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13206,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13206,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13206,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13206,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13206,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13206,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13206,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13206,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13206,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13206,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13206,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13206,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13206,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13206,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13206,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13206,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13206,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13206,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13206,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13206,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13206,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13206,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13206,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13206,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13206,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13206,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13206,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13206,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13206,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13206,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13206,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13206,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13206,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13206,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13206,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13206,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13206,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13206,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13206,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13206,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13206,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13206,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13206,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13206,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13206,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13206,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13206,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13206,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13206,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13206,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13206,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13206,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13206,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13206,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13206,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13206,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13206,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13206,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13206,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13206,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13206,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13206,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13206,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13206,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13206,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13206,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13206,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13206,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13206,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13206,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13206,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13206,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13206,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13206,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13206,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13206,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13206,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13206 : FrameRepair 13206 scalarRow13206 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13206Cells j).1 (repair13206Cells j).2.1
  endpoint_upper := fun j => ((repair13206Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13206Cells j).2.2

theorem repair13207Cells (j : Fin 43) :
    0 ≤ (scalarRow13207.table (sourceIndex j)).upper ∧
    (scalarRow13207.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13207.table (sourceIndex j)).centre) /
      (scalarRow13207.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13207.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13207,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13207,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13207,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13207,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13207,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13207,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13207,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13207,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13207,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13207,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13207,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13207,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13207,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13207,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13207,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13207,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13207,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13207,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13207,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13207,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13207,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13207,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13207,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13207,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13207,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13207,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13207,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13207,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13207,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13207,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13207,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13207,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13207,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13207,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13207,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13207,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13207,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13207,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13207,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13207,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13207,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13207,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13207,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13207,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13207,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13207,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13207,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13207,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13207,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13207,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13207,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13207,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13207,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13207,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13207,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13207,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13207,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13207,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13207,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13207,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13207,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13207,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13207,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13207,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13207,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13207,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13207,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13207,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13207,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13207,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13207,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13207,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13207,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13207,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13207,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13207,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13207,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13207,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13207,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13207,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13207,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13207,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13207,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13207,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13207,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13207,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13207 : FrameRepair 13207 scalarRow13207 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13207Cells j).1 (repair13207Cells j).2.1
  endpoint_upper := fun j => ((repair13207Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13207Cells j).2.2

theorem repair13208Cells (j : Fin 43) :
    0 ≤ (scalarRow13208.table (sourceIndex j)).upper ∧
    (scalarRow13208.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13208.table (sourceIndex j)).centre) /
      (scalarRow13208.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13208.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13208,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13208,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13208,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13208,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13208,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13208,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13208,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13208,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13208,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13208,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13208,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13208,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13208,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13208,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13208,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13208,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13208,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13208,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13208,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13208,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13208,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13208,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13208,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13208,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13208,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13208,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13208,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13208,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13208,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13208,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13208,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13208,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13208,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13208,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13208,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13208,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13208,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13208,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13208,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13208,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13208,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13208,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13208,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13208,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13208,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13208,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13208,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13208,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13208,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13208,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13208,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13208,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13208,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13208,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13208,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13208,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13208,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13208,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13208,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13208,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13208,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13208,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13208,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13208,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13208,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13208,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13208,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13208,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13208,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13208,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13208,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13208,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13208,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13208,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13208,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13208,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13208,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13208,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13208,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13208,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13208,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13208,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13208,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13208,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13208,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13208,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13208 : FrameRepair 13208 scalarRow13208 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13208Cells j).1 (repair13208Cells j).2.1
  endpoint_upper := fun j => ((repair13208Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13208Cells j).2.2

theorem repair13209Cells (j : Fin 43) :
    0 ≤ (scalarRow13209.table (sourceIndex j)).upper ∧
    (scalarRow13209.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13209.table (sourceIndex j)).centre) /
      (scalarRow13209.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13209.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13209,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13209,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13209,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13209,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13209,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13209,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13209,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13209,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13209,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13209,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13209,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13209,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13209,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13209,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13209,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13209,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13209,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13209,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13209,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13209,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13209,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13209,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13209,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13209,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13209,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13209,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13209,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13209,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13209,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13209,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13209,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13209,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13209,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13209,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13209,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13209,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13209,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13209,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13209,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13209,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13209,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13209,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13209,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13209,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13209,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13209,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13209,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13209,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13209,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13209,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13209,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13209,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13209,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13209,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13209,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13209,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13209,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13209,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13209,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13209,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13209,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13209,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13209,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13209,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13209,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13209,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13209,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13209,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13209,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13209,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13209,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13209,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13209,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13209,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13209,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13209,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13209,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13209,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13209,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13209,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13209,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13209,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13209,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13209,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13209,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13209,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13209 : FrameRepair 13209 scalarRow13209 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13209Cells j).1 (repair13209Cells j).2.1
  endpoint_upper := fun j => ((repair13209Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13209Cells j).2.2

theorem repair13210Cells (j : Fin 43) :
    0 ≤ (scalarRow13210.table (sourceIndex j)).upper ∧
    (scalarRow13210.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13210.table (sourceIndex j)).centre) /
      (scalarRow13210.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13210.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13210,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13210,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13210,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13210,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13210,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13210,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13210,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13210,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13210,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13210,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13210,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13210,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13210,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13210,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13210,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13210,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13210,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13210,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13210,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13210,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13210,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13210,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13210,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13210,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13210,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13210,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13210,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13210,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13210,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13210,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13210,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13210,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13210,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13210,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13210,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13210,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13210,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13210,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13210,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13210,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13210,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13210,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13210,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13210,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13210,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13210,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13210,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13210,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13210,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13210,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13210,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13210,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13210,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13210,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13210,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13210,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13210,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13210,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13210,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13210,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13210,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13210,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13210,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13210,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13210,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13210,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13210,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13210,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13210,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13210,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13210,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13210,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13210,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13210,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13210,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13210,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13210,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13210,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13210,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13210,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13210,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13210,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13210,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13210,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13210,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13210,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13210 : FrameRepair 13210 scalarRow13210 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13210Cells j).1 (repair13210Cells j).2.1
  endpoint_upper := fun j => ((repair13210Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13210Cells j).2.2

theorem repair13211Cells (j : Fin 43) :
    0 ≤ (scalarRow13211.table (sourceIndex j)).upper ∧
    (scalarRow13211.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13211.table (sourceIndex j)).centre) /
      (scalarRow13211.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13211.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13211,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13211,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13211,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13211,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13211,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13211,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13211,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13211,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13211,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13211,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13211,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13211,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13211,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13211,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13211,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13211,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13211,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13211,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13211,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13211,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13211,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13211,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13211,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13211,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13211,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13211,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13211,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13211,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13211,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13211,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13211,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13211,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13211,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13211,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13211,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13211,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13211,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13211,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13211,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13211,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13211,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13211,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13211,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13211,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13211,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13211,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13211,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13211,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13211,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13211,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13211,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13211,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13211,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13211,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13211,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13211,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13211,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13211,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13211,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13211,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13211,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13211,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13211,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13211,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13211,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13211,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13211,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13211,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13211,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13211,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13211,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13211,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13211,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13211,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13211,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13211,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13211,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13211,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13211,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13211,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13211,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13211,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13211,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13211,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13211,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13211,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13211 : FrameRepair 13211 scalarRow13211 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13211Cells j).1 (repair13211Cells j).2.1
  endpoint_upper := fun j => ((repair13211Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13211Cells j).2.2

theorem repair13212Cells (j : Fin 43) :
    0 ≤ (scalarRow13212.table (sourceIndex j)).upper ∧
    (scalarRow13212.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13212.table (sourceIndex j)).centre) /
      (scalarRow13212.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13212.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13212,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13212,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13212,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13212,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13212,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13212,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13212,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13212,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13212,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13212,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13212,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13212,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13212,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13212,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13212,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13212,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13212,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13212,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13212,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13212,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13212,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13212,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13212,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13212,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13212,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13212,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13212,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13212,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13212,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13212,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13212,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13212,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13212,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13212,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13212,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13212,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13212,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13212,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13212,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13212,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13212,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13212,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13212,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13212,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13212,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13212,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13212,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13212,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13212,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13212,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13212,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13212,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13212,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13212,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13212,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13212,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13212,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13212,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13212,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13212,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13212,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13212,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13212,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13212,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13212,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13212,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13212,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13212,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13212,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13212,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13212,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13212,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13212,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13212,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13212,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13212,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13212,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13212,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13212,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13212,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13212,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13212,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13212,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13212,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13212,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13212,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13212 : FrameRepair 13212 scalarRow13212 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13212Cells j).1 (repair13212Cells j).2.1
  endpoint_upper := fun j => ((repair13212Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13212Cells j).2.2

theorem repair13213Cells (j : Fin 43) :
    0 ≤ (scalarRow13213.table (sourceIndex j)).upper ∧
    (scalarRow13213.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13213.table (sourceIndex j)).centre) /
      (scalarRow13213.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13213.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13213,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13213,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13213,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13213,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13213,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13213,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13213,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13213,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13213,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13213,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13213,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13213,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13213,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13213,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13213,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13213,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13213,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13213,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13213,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13213,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13213,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13213,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13213,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13213,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13213,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13213,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13213,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13213,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13213,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13213,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13213,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13213,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13213,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13213,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13213,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13213,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13213,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13213,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13213,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13213,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13213,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13213,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13213,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13213,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13213,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13213,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13213,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13213,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13213,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13213,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13213,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13213,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13213,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13213,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13213,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13213,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13213,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13213,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13213,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13213,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13213,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13213,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13213,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13213,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13213,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13213,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13213,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13213,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13213,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13213,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13213,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13213,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13213,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13213,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13213,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13213,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13213,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13213,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13213,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13213,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13213,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13213,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13213,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13213,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13213,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13213,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13213 : FrameRepair 13213 scalarRow13213 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13213Cells j).1 (repair13213Cells j).2.1
  endpoint_upper := fun j => ((repair13213Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13213Cells j).2.2

theorem repair13214Cells (j : Fin 43) :
    0 ≤ (scalarRow13214.table (sourceIndex j)).upper ∧
    (scalarRow13214.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13214.table (sourceIndex j)).centre) /
      (scalarRow13214.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13214.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13214,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13214,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13214,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13214,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13214,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13214,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13214,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13214,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13214,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13214,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13214,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13214,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13214,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13214,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13214,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13214,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13214,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13214,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13214,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13214,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13214,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13214,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13214,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13214,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13214,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13214,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13214,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13214,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13214,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13214,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13214,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13214,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13214,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13214,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13214,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13214,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13214,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13214,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13214,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13214,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13214,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13214,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13214,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13214,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13214,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13214,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13214,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13214,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13214,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13214,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13214,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13214,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13214,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13214,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13214,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13214,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13214,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13214,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13214,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13214,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13214,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13214,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13214,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13214,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13214,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13214,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13214,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13214,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13214,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13214,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13214,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13214,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13214,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13214,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13214,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13214,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13214,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13214,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13214,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13214,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13214,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13214,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13214,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13214,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13214,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13214,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13214 : FrameRepair 13214 scalarRow13214 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13214Cells j).1 (repair13214Cells j).2.1
  endpoint_upper := fun j => ((repair13214Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13214Cells j).2.2

theorem repair13215Cells (j : Fin 43) :
    0 ≤ (scalarRow13215.table (sourceIndex j)).upper ∧
    (scalarRow13215.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13215.table (sourceIndex j)).centre) /
      (scalarRow13215.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13215.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13215,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13215,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13215,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13215,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13215,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13215,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13215,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13215,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13215,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13215,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13215,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13215,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13215,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13215,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13215,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13215,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13215,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13215,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13215,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13215,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13215,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13215,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13215,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13215,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13215,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13215,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13215,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13215,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13215,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13215,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13215,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13215,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13215,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13215,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13215,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13215,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13215,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13215,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13215,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13215,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13215,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13215,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13215,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13215,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13215,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13215,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13215,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13215,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13215,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13215,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13215,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13215,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13215,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13215,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13215,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13215,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13215,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13215,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13215,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13215,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13215,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13215,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13215,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13215,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13215,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13215,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13215,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13215,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13215,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13215,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13215,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13215,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13215,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13215,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13215,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13215,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13215,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13215,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13215,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13215,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13215,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13215,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13215,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13215,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13215,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13215,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13215 : FrameRepair 13215 scalarRow13215 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13215Cells j).1 (repair13215Cells j).2.1
  endpoint_upper := fun j => ((repair13215Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13215Cells j).2.2

theorem repair13216Cells (j : Fin 43) :
    0 ≤ (scalarRow13216.table (sourceIndex j)).upper ∧
    (scalarRow13216.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13216.table (sourceIndex j)).centre) /
      (scalarRow13216.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13216.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13216,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13216,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13216,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13216,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13216,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13216,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13216,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13216,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13216,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13216,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13216,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13216,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13216,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13216,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13216,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13216,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13216,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13216,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13216,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13216,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13216,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13216,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13216,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13216,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13216,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13216,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13216,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13216,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13216,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13216,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13216,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13216,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13216,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13216,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13216,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13216,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13216,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13216,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13216,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13216,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13216,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13216,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13216,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13216,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13216,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13216,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13216,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13216,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13216,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13216,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13216,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13216,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13216,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13216,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13216,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13216,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13216,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13216,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13216,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13216,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13216,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13216,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13216,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13216,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13216,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13216,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13216,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13216,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13216,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13216,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13216,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13216,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13216,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13216,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13216,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13216,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13216,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13216,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13216,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13216,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13216,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13216,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13216,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13216,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13216,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13216,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13216 : FrameRepair 13216 scalarRow13216 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13216Cells j).1 (repair13216Cells j).2.1
  endpoint_upper := fun j => ((repair13216Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13216Cells j).2.2

theorem repair13217Cells (j : Fin 43) :
    0 ≤ (scalarRow13217.table (sourceIndex j)).upper ∧
    (scalarRow13217.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13217.table (sourceIndex j)).centre) /
      (scalarRow13217.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13217.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13217,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13217,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13217,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13217,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13217,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13217,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13217,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13217,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13217,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13217,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13217,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13217,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13217,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13217,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13217,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13217,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13217,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13217,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13217,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13217,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13217,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13217,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13217,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13217,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13217,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13217,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13217,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13217,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13217,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13217,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13217,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13217,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13217,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13217,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13217,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13217,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13217,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13217,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13217,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13217,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13217,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13217,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13217,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13217,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13217,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13217,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13217,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13217,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13217,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13217,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13217,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13217,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13217,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13217,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13217,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13217,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13217,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13217,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13217,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13217,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13217,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13217,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13217,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13217,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13217,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13217,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13217,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13217,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13217,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13217,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13217,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13217,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13217,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13217,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13217,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13217,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13217,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13217,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13217,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13217,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13217,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13217,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13217,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13217,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13217,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13217,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13217 : FrameRepair 13217 scalarRow13217 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13217Cells j).1 (repair13217Cells j).2.1
  endpoint_upper := fun j => ((repair13217Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13217Cells j).2.2

theorem repair13218Cells (j : Fin 43) :
    0 ≤ (scalarRow13218.table (sourceIndex j)).upper ∧
    (scalarRow13218.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13218.table (sourceIndex j)).centre) /
      (scalarRow13218.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13218.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13218,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13218,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13218,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13218,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13218,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13218,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13218,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13218,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13218,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13218,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13218,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13218,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13218,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13218,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13218,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13218,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13218,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13218,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13218,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13218,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13218,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13218,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13218,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13218,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13218,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13218,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13218,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13218,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13218,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13218,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13218,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13218,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13218,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13218,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13218,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13218,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13218,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13218,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13218,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13218,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13218,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13218,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13218,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13218,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13218,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13218,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13218,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13218,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13218,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13218,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13218,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13218,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13218,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13218,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13218,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13218,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13218,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13218,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13218,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13218,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13218,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13218,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13218,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13218,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13218,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13218,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13218,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13218,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13218,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13218,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13218,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13218,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13218,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13218,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13218,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13218,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13218,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13218,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13218,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13218,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13218,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13218,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13218,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13218,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13218,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13218,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13218 : FrameRepair 13218 scalarRow13218 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13218Cells j).1 (repair13218Cells j).2.1
  endpoint_upper := fun j => ((repair13218Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13218Cells j).2.2

theorem repair13219Cells (j : Fin 43) :
    0 ≤ (scalarRow13219.table (sourceIndex j)).upper ∧
    (scalarRow13219.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13219.table (sourceIndex j)).centre) /
      (scalarRow13219.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13219.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13219,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13219,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13219,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13219,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13219,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13219,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13219,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13219,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13219,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13219,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13219,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13219,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13219,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13219,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13219,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13219,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13219,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13219,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13219,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13219,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13219,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13219,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13219,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13219,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13219,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13219,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13219,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13219,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13219,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13219,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13219,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13219,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13219,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13219,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13219,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13219,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13219,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13219,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13219,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13219,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13219,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13219,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13219,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13219,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13219,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13219,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13219,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13219,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13219,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13219,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13219,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13219,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13219,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13219,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13219,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13219,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13219,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13219,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13219,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13219,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13219,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13219,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13219,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13219,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13219,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13219,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13219,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13219,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13219,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13219,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13219,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13219,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13219,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13219,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13219,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13219,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13219,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13219,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13219,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13219,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13219,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13219,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13219,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13219,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13219,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13219,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13219 : FrameRepair 13219 scalarRow13219 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13219Cells j).1 (repair13219Cells j).2.1
  endpoint_upper := fun j => ((repair13219Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13219Cells j).2.2

theorem repair13220Cells (j : Fin 43) :
    0 ≤ (scalarRow13220.table (sourceIndex j)).upper ∧
    (scalarRow13220.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13220.table (sourceIndex j)).centre) /
      (scalarRow13220.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13220.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13220,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13220,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13220,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13220,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13220,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13220,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13220,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13220,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13220,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13220,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13220,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13220,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13220,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13220,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13220,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13220,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13220,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13220,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13220,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13220,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13220,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13220,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13220,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13220,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13220,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13220,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13220,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13220,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13220,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13220,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13220,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13220,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13220,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13220,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13220,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13220,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13220,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13220,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13220,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13220,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13220,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13220,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13220,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13220,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13220,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13220,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13220,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13220,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13220,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13220,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13220,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13220,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13220,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13220,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13220,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13220,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13220,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13220,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13220,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13220,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13220,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13220,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13220,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13220,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13220,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13220,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13220,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13220,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13220,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13220,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13220,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13220,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13220,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13220,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13220,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13220,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13220,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13220,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13220,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13220,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13220,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13220,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13220,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13220,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13220,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13220,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13220 : FrameRepair 13220 scalarRow13220 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13220Cells j).1 (repair13220Cells j).2.1
  endpoint_upper := fun j => ((repair13220Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13220Cells j).2.2

theorem repair13221Cells (j : Fin 43) :
    0 ≤ (scalarRow13221.table (sourceIndex j)).upper ∧
    (scalarRow13221.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13221.table (sourceIndex j)).centre) /
      (scalarRow13221.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13221.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13221,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13221,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13221,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13221,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13221,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13221,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13221,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13221,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13221,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13221,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13221,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13221,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13221,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13221,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13221,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13221,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13221,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13221,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13221,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13221,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13221,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13221,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13221,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13221,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13221,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13221,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13221,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13221,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13221,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13221,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13221,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13221,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13221,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13221,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13221,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13221,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13221,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13221,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13221,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13221,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13221,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13221,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13221,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13221,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13221,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13221,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13221,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13221,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13221,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13221,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13221,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13221,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13221,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13221,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13221,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13221,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13221,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13221,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13221,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13221,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13221,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13221,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13221,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13221,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13221,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13221,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13221,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13221,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13221,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13221,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13221,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13221,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13221,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13221,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13221,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13221,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13221,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13221,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13221,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13221,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13221,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13221,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13221,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13221,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13221,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13221,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13221 : FrameRepair 13221 scalarRow13221 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13221Cells j).1 (repair13221Cells j).2.1
  endpoint_upper := fun j => ((repair13221Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13221Cells j).2.2

theorem repair13222Cells (j : Fin 43) :
    0 ≤ (scalarRow13222.table (sourceIndex j)).upper ∧
    (scalarRow13222.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13222.table (sourceIndex j)).centre) /
      (scalarRow13222.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13222.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13222,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13222,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13222,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13222,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13222,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13222,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13222,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13222,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13222,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13222,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13222,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13222,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13222,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13222,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13222,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13222,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13222,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13222,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13222,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13222,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13222,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13222,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13222,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13222,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13222,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13222,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13222,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13222,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13222,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13222,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13222,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13222,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13222,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13222,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13222,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13222,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13222,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13222,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13222,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13222,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13222,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13222,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13222,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13222,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13222,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13222,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13222,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13222,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13222,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13222,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13222,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13222,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13222,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13222,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13222,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13222,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13222,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13222,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13222,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13222,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13222,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13222,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13222,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13222,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13222,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13222,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13222,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13222,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13222,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13222,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13222,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13222,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13222,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13222,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13222,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13222,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13222,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13222,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13222,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13222,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13222,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13222,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13222,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13222,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13222,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13222,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13222 : FrameRepair 13222 scalarRow13222 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13222Cells j).1 (repair13222Cells j).2.1
  endpoint_upper := fun j => ((repair13222Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13222Cells j).2.2

theorem repair13223Cells (j : Fin 43) :
    0 ≤ (scalarRow13223.table (sourceIndex j)).upper ∧
    (scalarRow13223.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13223.table (sourceIndex j)).centre) /
      (scalarRow13223.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13223.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13223,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13223,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13223,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13223,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13223,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13223,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13223,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13223,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13223,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13223,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13223,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13223,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13223,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13223,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13223,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13223,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13223,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13223,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13223,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13223,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13223,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13223,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13223,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13223,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13223,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13223,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13223,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13223,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13223,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13223,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13223,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13223,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13223,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13223,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13223,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13223,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13223,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13223,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13223,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13223,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13223,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13223,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13223,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13223,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13223,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13223,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13223,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13223,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13223,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13223,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13223,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13223,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13223,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13223,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13223,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13223,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13223,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13223,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13223,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13223,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13223,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13223,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13223,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13223,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13223,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13223,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13223,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13223,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13223,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13223,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13223,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13223,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13223,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13223,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13223,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13223,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13223,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13223,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13223,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13223,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13223,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13223,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13223,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13223,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13223,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13223,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13223 : FrameRepair 13223 scalarRow13223 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13223Cells j).1 (repair13223Cells j).2.1
  endpoint_upper := fun j => ((repair13223Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13223Cells j).2.2

end BstLean.Part269
