import BstLean.Part269Rows7
import BstLean.Part269RepairCommon
namespace BstLean.Part269
open Real Set BstLean.Part255 BstLean.Part263 BstLean.Part264
theorem repair12525Cells (j : Fin 43) :
    0 ≤ (scalarRow12525.table (sourceIndex j)).upper ∧
    (scalarRow12525.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12525.table (sourceIndex j)).centre) /
      (scalarRow12525.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12525.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12525,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12525,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12525,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12525,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12525,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12525,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12525,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12525,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12525,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12525,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12525,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12525,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12525,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12525,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12525,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12525,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12525,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12525,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12525,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12525,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12525,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12525,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12525,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12525,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12525,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12525,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12525,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12525,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12525,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12525,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12525,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12525,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12525,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12525,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12525,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12525,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12525,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12525,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12525,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12525,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12525,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12525,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12525,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12525,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12525,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12525,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12525,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12525,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12525,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12525,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12525,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12525,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12525,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12525,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12525,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12525,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12525,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12525,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12525,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12525,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12525,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12525,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12525,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12525,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12525,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12525,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12525,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12525,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12525,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12525,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12525,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12525,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12525,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12525,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12525,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12525,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12525,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12525,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12525,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12525,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12525,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12525,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12525,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12525,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12525,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12525,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12525 : FrameRepair 12525 scalarRow12525 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12525Cells j).1 (repair12525Cells j).2.1
  endpoint_upper := fun j => ((repair12525Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12525Cells j).2.2

theorem repair12526Cells (j : Fin 43) :
    0 ≤ (scalarRow12526.table (sourceIndex j)).upper ∧
    (scalarRow12526.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12526.table (sourceIndex j)).centre) /
      (scalarRow12526.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12526.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12526,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12526,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12526,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12526,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12526,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12526,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12526,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12526,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12526,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12526,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12526,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12526,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12526,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12526,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12526,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12526,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12526,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12526,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12526,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12526,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12526,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12526,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12526,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12526,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12526,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12526,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12526,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12526,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12526,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12526,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12526,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12526,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12526,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12526,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12526,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12526,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12526,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12526,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12526,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12526,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12526,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12526,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12526,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12526,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12526,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12526,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12526,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12526,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12526,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12526,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12526,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12526,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12526,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12526,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12526,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12526,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12526,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12526,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12526,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12526,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12526,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12526,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12526,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12526,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12526,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12526,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12526,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12526,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12526,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12526,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12526,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12526,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12526,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12526,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12526,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12526,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12526,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12526,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12526,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12526,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12526,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12526,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12526,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12526,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12526,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12526,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12526 : FrameRepair 12526 scalarRow12526 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12526Cells j).1 (repair12526Cells j).2.1
  endpoint_upper := fun j => ((repair12526Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12526Cells j).2.2

theorem repair12527Cells (j : Fin 43) :
    0 ≤ (scalarRow12527.table (sourceIndex j)).upper ∧
    (scalarRow12527.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12527.table (sourceIndex j)).centre) /
      (scalarRow12527.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12527.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12527,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12527,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12527,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12527,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12527,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12527,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12527,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12527,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12527,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12527,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12527,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12527,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12527,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12527,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12527,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12527,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12527,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12527,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12527,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12527,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12527,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12527,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12527,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12527,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12527,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12527,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12527,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12527,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12527,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12527,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12527,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12527,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12527,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12527,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12527,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12527,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12527,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12527,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12527,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12527,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12527,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12527,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12527,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12527,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12527,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12527,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12527,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12527,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12527,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12527,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12527,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12527,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12527,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12527,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12527,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12527,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12527,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12527,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12527,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12527,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12527,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12527,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12527,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12527,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12527,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12527,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12527,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12527,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12527,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12527,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12527,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12527,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12527,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12527,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12527,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12527,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12527,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12527,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12527,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12527,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12527,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12527,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12527,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12527,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12527,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12527,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12527 : FrameRepair 12527 scalarRow12527 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12527Cells j).1 (repair12527Cells j).2.1
  endpoint_upper := fun j => ((repair12527Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12527Cells j).2.2

theorem repair12528Cells (j : Fin 43) :
    0 ≤ (scalarRow12528.table (sourceIndex j)).upper ∧
    (scalarRow12528.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12528.table (sourceIndex j)).centre) /
      (scalarRow12528.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12528.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12528,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12528,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12528,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12528,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12528,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12528,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12528,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12528,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12528,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12528,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12528,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12528,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12528,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12528,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12528,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12528,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12528,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12528,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12528,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12528,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12528,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12528,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12528,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12528,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12528,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12528,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12528,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12528,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12528,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12528,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12528,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12528,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12528,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12528,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12528,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12528,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12528,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12528,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12528,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12528,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12528,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12528,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12528,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12528,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12528,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12528,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12528,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12528,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12528,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12528,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12528,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12528,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12528,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12528,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12528,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12528,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12528,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12528,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12528,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12528,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12528,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12528,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12528,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12528,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12528,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12528,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12528,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12528,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12528,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12528,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12528,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12528,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12528,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12528,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12528,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12528,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12528,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12528,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12528,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12528,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12528,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12528,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12528,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12528,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12528,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12528,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12528 : FrameRepair 12528 scalarRow12528 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12528Cells j).1 (repair12528Cells j).2.1
  endpoint_upper := fun j => ((repair12528Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12528Cells j).2.2

theorem repair12529Cells (j : Fin 43) :
    0 ≤ (scalarRow12529.table (sourceIndex j)).upper ∧
    (scalarRow12529.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12529.table (sourceIndex j)).centre) /
      (scalarRow12529.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12529.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12529,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12529,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12529,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12529,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12529,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12529,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12529,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12529,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12529,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12529,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12529,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12529,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12529,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12529,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12529,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12529,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12529,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12529,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12529,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12529,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12529,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12529,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12529,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12529,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12529,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12529,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12529,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12529,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12529,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12529,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12529,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12529,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12529,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12529,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12529,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12529,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12529,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12529,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12529,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12529,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12529,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12529,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12529,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12529,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12529,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12529,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12529,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12529,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12529,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12529,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12529,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12529,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12529,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12529,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12529,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12529,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12529,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12529,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12529,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12529,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12529,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12529,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12529,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12529,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12529,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12529,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12529,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12529,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12529,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12529,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12529,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12529,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12529,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12529,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12529,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12529,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12529,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12529,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12529,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12529,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12529,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12529,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12529,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12529,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12529,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12529,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12529 : FrameRepair 12529 scalarRow12529 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12529Cells j).1 (repair12529Cells j).2.1
  endpoint_upper := fun j => ((repair12529Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12529Cells j).2.2

theorem repair12530Cells (j : Fin 43) :
    0 ≤ (scalarRow12530.table (sourceIndex j)).upper ∧
    (scalarRow12530.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12530.table (sourceIndex j)).centre) /
      (scalarRow12530.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12530.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12530,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12530,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12530,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12530,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12530,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12530,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12530,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12530,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12530,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12530,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12530,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12530,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12530,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12530,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12530,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12530,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12530,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12530,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12530,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12530,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12530,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12530,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12530,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12530,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12530,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12530,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12530,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12530,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12530,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12530,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12530,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12530,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12530,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12530,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12530,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12530,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12530,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12530,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12530,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12530,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12530,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12530,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12530,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12530,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12530,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12530,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12530,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12530,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12530,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12530,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12530,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12530,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12530,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12530,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12530,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12530,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12530,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12530,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12530,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12530,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12530,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12530,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12530,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12530,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12530,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12530,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12530,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12530,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12530,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12530,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12530,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12530,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12530,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12530,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12530,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12530,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12530,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12530,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12530,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12530,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12530,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12530,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12530,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12530,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12530,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12530,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12530 : FrameRepair 12530 scalarRow12530 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12530Cells j).1 (repair12530Cells j).2.1
  endpoint_upper := fun j => ((repair12530Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12530Cells j).2.2

theorem repair12531Cells (j : Fin 43) :
    0 ≤ (scalarRow12531.table (sourceIndex j)).upper ∧
    (scalarRow12531.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12531.table (sourceIndex j)).centre) /
      (scalarRow12531.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12531.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12531,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12531,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12531,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12531,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12531,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12531,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12531,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12531,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12531,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12531,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12531,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12531,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12531,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12531,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12531,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12531,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12531,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12531,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12531,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12531,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12531,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12531,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12531,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12531,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12531,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12531,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12531,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12531,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12531,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12531,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12531,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12531,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12531,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12531,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12531,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12531,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12531,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12531,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12531,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12531,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12531,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12531,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12531,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12531,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12531,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12531,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12531,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12531,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12531,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12531,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12531,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12531,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12531,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12531,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12531,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12531,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12531,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12531,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12531,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12531,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12531,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12531,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12531,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12531,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12531,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12531,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12531,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12531,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12531,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12531,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12531,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12531,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12531,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12531,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12531,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12531,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12531,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12531,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12531,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12531,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12531,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12531,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12531,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12531,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12531,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12531,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12531 : FrameRepair 12531 scalarRow12531 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12531Cells j).1 (repair12531Cells j).2.1
  endpoint_upper := fun j => ((repair12531Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12531Cells j).2.2

theorem repair12532Cells (j : Fin 43) :
    0 ≤ (scalarRow12532.table (sourceIndex j)).upper ∧
    (scalarRow12532.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12532.table (sourceIndex j)).centre) /
      (scalarRow12532.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12532.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12532,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12532,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12532,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12532,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12532,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12532,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12532,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12532,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12532,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12532,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12532,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12532,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12532,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12532,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12532,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12532,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12532,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12532,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12532,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12532,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12532,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12532,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12532,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12532,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12532,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12532,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12532,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12532,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12532,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12532,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12532,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12532,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12532,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12532,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12532,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12532,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12532,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12532,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12532,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12532,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12532,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12532,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12532,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12532,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12532,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12532,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12532,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12532,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12532,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12532,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12532,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12532,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12532,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12532,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12532,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12532,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12532,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12532,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12532,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12532,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12532,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12532,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12532,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12532,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12532,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12532,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12532,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12532,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12532,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12532,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12532,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12532,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12532,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12532,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12532,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12532,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12532,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12532,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12532,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12532,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12532,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12532,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12532,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12532,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12532,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12532,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12532 : FrameRepair 12532 scalarRow12532 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12532Cells j).1 (repair12532Cells j).2.1
  endpoint_upper := fun j => ((repair12532Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12532Cells j).2.2

theorem repair12533Cells (j : Fin 43) :
    0 ≤ (scalarRow12533.table (sourceIndex j)).upper ∧
    (scalarRow12533.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12533.table (sourceIndex j)).centre) /
      (scalarRow12533.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12533.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12533,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12533,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12533,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12533,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12533,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12533,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12533,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12533,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12533,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12533,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12533,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12533,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12533,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12533,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12533,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12533,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12533,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12533,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12533,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12533,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12533,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12533,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12533,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12533,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12533,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12533,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12533,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12533,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12533,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12533,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12533,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12533,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12533,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12533,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12533,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12533,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12533,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12533,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12533,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12533,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12533,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12533,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12533,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12533,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12533,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12533,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12533,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12533,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12533,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12533,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12533,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12533,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12533,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12533,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12533,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12533,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12533,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12533,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12533,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12533,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12533,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12533,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12533,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12533,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12533,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12533,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12533,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12533,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12533,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12533,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12533,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12533,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12533,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12533,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12533,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12533,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12533,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12533,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12533,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12533,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12533,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12533,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12533,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12533,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12533,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12533,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12533 : FrameRepair 12533 scalarRow12533 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12533Cells j).1 (repair12533Cells j).2.1
  endpoint_upper := fun j => ((repair12533Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12533Cells j).2.2

theorem repair12534Cells (j : Fin 43) :
    0 ≤ (scalarRow12534.table (sourceIndex j)).upper ∧
    (scalarRow12534.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12534.table (sourceIndex j)).centre) /
      (scalarRow12534.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12534.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12534,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12534,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12534,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12534,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12534,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12534,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12534,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12534,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12534,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12534,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12534,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12534,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12534,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12534,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12534,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12534,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12534,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12534,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12534,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12534,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12534,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12534,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12534,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12534,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12534,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12534,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12534,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12534,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12534,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12534,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12534,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12534,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12534,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12534,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12534,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12534,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12534,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12534,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12534,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12534,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12534,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12534,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12534,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12534,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12534,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12534,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12534,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12534,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12534,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12534,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12534,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12534,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12534,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12534,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12534,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12534,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12534,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12534,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12534,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12534,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12534,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12534,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12534,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12534,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12534,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12534,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12534,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12534,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12534,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12534,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12534,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12534,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12534,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12534,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12534,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12534,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12534,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12534,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12534,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12534,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12534,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12534,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12534,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12534,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12534,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12534,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12534 : FrameRepair 12534 scalarRow12534 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12534Cells j).1 (repair12534Cells j).2.1
  endpoint_upper := fun j => ((repair12534Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12534Cells j).2.2

theorem repair12535Cells (j : Fin 43) :
    0 ≤ (scalarRow12535.table (sourceIndex j)).upper ∧
    (scalarRow12535.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12535.table (sourceIndex j)).centre) /
      (scalarRow12535.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12535.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12535,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12535,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12535,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12535,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12535,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12535,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12535,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12535,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12535,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12535,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12535,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12535,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12535,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12535,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12535,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12535,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12535,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12535,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12535,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12535,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12535,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12535,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12535,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12535,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12535,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12535,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12535,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12535,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12535,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12535,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12535,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12535,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12535,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12535,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12535,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12535,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12535,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12535,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12535,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12535,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12535,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12535,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12535,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12535,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12535,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12535,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12535,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12535,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12535,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12535,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12535,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12535,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12535,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12535,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12535,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12535,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12535,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12535,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12535,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12535,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12535,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12535,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12535,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12535,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12535,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12535,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12535,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12535,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12535,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12535,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12535,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12535,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12535,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12535,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12535,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12535,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12535,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12535,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12535,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12535,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12535,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12535,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12535,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12535,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12535,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12535,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12535 : FrameRepair 12535 scalarRow12535 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12535Cells j).1 (repair12535Cells j).2.1
  endpoint_upper := fun j => ((repair12535Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12535Cells j).2.2

theorem repair12536Cells (j : Fin 43) :
    0 ≤ (scalarRow12536.table (sourceIndex j)).upper ∧
    (scalarRow12536.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12536.table (sourceIndex j)).centre) /
      (scalarRow12536.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12536.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12536,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12536,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12536,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12536,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12536,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12536,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12536,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12536,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12536,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12536,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12536,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12536,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12536,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12536,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12536,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12536,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12536,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12536,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12536,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12536,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12536,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12536,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12536,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12536,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12536,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12536,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12536,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12536,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12536,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12536,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12536,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12536,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12536,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12536,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12536,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12536,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12536,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12536,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12536,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12536,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12536,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12536,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12536,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12536,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12536,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12536,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12536,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12536,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12536,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12536,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12536,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12536,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12536,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12536,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12536,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12536,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12536,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12536,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12536,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12536,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12536,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12536,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12536,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12536,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12536,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12536,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12536,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12536,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12536,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12536,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12536,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12536,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12536,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12536,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12536,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12536,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12536,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12536,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12536,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12536,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12536,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12536,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12536,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12536,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12536,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12536,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12536 : FrameRepair 12536 scalarRow12536 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12536Cells j).1 (repair12536Cells j).2.1
  endpoint_upper := fun j => ((repair12536Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12536Cells j).2.2

theorem repair12537Cells (j : Fin 43) :
    0 ≤ (scalarRow12537.table (sourceIndex j)).upper ∧
    (scalarRow12537.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12537.table (sourceIndex j)).centre) /
      (scalarRow12537.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12537.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12537,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12537,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12537,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12537,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12537,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12537,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12537,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12537,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12537,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12537,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12537,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12537,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12537,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12537,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12537,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12537,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12537,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12537,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12537,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12537,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12537,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12537,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12537,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12537,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12537,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12537,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12537,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12537,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12537,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12537,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12537,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12537,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12537,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12537,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12537,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12537,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12537,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12537,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12537,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12537,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12537,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12537,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12537,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12537,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12537,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12537,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12537,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12537,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12537,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12537,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12537,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12537,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12537,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12537,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12537,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12537,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12537,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12537,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12537,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12537,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12537,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12537,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12537,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12537,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12537,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12537,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12537,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12537,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12537,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12537,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12537,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12537,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12537,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12537,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12537,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12537,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12537,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12537,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12537,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12537,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12537,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12537,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12537,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12537,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12537,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12537,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12537 : FrameRepair 12537 scalarRow12537 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12537Cells j).1 (repair12537Cells j).2.1
  endpoint_upper := fun j => ((repair12537Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12537Cells j).2.2

theorem repair12538Cells (j : Fin 43) :
    0 ≤ (scalarRow12538.table (sourceIndex j)).upper ∧
    (scalarRow12538.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12538.table (sourceIndex j)).centre) /
      (scalarRow12538.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12538.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12538,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12538,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12538,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12538,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12538,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12538,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12538,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12538,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12538,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12538,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12538,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12538,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12538,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12538,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12538,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12538,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12538,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12538,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12538,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12538,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12538,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12538,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12538,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12538,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12538,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12538,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12538,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12538,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12538,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12538,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12538,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12538,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12538,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12538,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12538,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12538,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12538,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12538,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12538,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12538,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12538,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12538,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12538,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12538,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12538,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12538,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12538,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12538,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12538,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12538,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12538,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12538,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12538,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12538,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12538,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12538,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12538,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12538,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12538,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12538,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12538,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12538,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12538,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12538,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12538,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12538,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12538,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12538,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12538,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12538,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12538,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12538,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12538,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12538,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12538,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12538,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12538,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12538,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12538,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12538,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12538,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12538,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12538,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12538,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12538,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12538,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12538 : FrameRepair 12538 scalarRow12538 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12538Cells j).1 (repair12538Cells j).2.1
  endpoint_upper := fun j => ((repair12538Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12538Cells j).2.2

theorem repair12539Cells (j : Fin 43) :
    0 ≤ (scalarRow12539.table (sourceIndex j)).upper ∧
    (scalarRow12539.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12539.table (sourceIndex j)).centre) /
      (scalarRow12539.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12539.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12539,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12539,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12539,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12539,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12539,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12539,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12539,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12539,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12539,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12539,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12539,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12539,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12539,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12539,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12539,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12539,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12539,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12539,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12539,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12539,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12539,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12539,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12539,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12539,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12539,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12539,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12539,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12539,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12539,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12539,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12539,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12539,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12539,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12539,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12539,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12539,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12539,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12539,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12539,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12539,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12539,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12539,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12539,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12539,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12539,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12539,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12539,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12539,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12539,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12539,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12539,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12539,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12539,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12539,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12539,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12539,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12539,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12539,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12539,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12539,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12539,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12539,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12539,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12539,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12539,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12539,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12539,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12539,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12539,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12539,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12539,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12539,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12539,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12539,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12539,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12539,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12539,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12539,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12539,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12539,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12539,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12539,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12539,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12539,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12539,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12539,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12539 : FrameRepair 12539 scalarRow12539 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12539Cells j).1 (repair12539Cells j).2.1
  endpoint_upper := fun j => ((repair12539Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12539Cells j).2.2

theorem repair12540Cells (j : Fin 43) :
    0 ≤ (scalarRow12540.table (sourceIndex j)).upper ∧
    (scalarRow12540.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12540.table (sourceIndex j)).centre) /
      (scalarRow12540.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12540.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12540,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12540,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12540,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12540,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12540,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12540,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12540,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12540,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12540,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12540,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12540,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12540,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12540,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12540,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12540,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12540,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12540,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12540,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12540,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12540,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12540,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12540,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12540,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12540,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12540,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12540,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12540,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12540,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12540,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12540,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12540,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12540,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12540,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12540,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12540,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12540,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12540,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12540,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12540,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12540,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12540,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12540,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12540,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12540,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12540,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12540,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12540,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12540,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12540,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12540,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12540,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12540,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12540,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12540,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12540,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12540,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12540,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12540,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12540,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12540,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12540,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12540,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12540,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12540,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12540,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12540,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12540,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12540,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12540,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12540,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12540,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12540,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12540,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12540,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12540,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12540,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12540,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12540,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12540,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12540,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12540,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12540,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12540,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12540,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12540,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12540,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12540 : FrameRepair 12540 scalarRow12540 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12540Cells j).1 (repair12540Cells j).2.1
  endpoint_upper := fun j => ((repair12540Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12540Cells j).2.2

theorem repair12541Cells (j : Fin 43) :
    0 ≤ (scalarRow12541.table (sourceIndex j)).upper ∧
    (scalarRow12541.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12541.table (sourceIndex j)).centre) /
      (scalarRow12541.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12541.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12541,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12541,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12541,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12541,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12541,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12541,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12541,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12541,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12541,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12541,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12541,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12541,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12541,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12541,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12541,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12541,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12541,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12541,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12541,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12541,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12541,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12541,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12541,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12541,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12541,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12541,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12541,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12541,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12541,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12541,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12541,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12541,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12541,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12541,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12541,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12541,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12541,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12541,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12541,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12541,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12541,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12541,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12541,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12541,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12541,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12541,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12541,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12541,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12541,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12541,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12541,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12541,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12541,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12541,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12541,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12541,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12541,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12541,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12541,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12541,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12541,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12541,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12541,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12541,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12541,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12541,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12541,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12541,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12541,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12541,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12541,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12541,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12541,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12541,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12541,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12541,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12541,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12541,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12541,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12541,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12541,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12541,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12541,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12541,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12541,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12541,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12541 : FrameRepair 12541 scalarRow12541 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12541Cells j).1 (repair12541Cells j).2.1
  endpoint_upper := fun j => ((repair12541Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12541Cells j).2.2

theorem repair12542Cells (j : Fin 43) :
    0 ≤ (scalarRow12542.table (sourceIndex j)).upper ∧
    (scalarRow12542.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12542.table (sourceIndex j)).centre) /
      (scalarRow12542.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12542.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12542,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12542,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12542,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12542,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12542,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12542,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12542,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12542,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12542,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12542,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12542,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12542,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12542,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12542,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12542,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12542,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12542,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12542,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12542,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12542,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12542,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12542,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12542,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12542,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12542,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12542,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12542,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12542,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12542,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12542,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12542,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12542,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12542,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12542,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12542,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12542,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12542,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12542,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12542,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12542,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12542,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12542,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12542,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12542,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12542,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12542,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12542,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12542,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12542,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12542,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12542,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12542,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12542,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12542,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12542,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12542,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12542,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12542,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12542,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12542,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12542,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12542,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12542,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12542,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12542,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12542,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12542,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12542,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12542,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12542,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12542,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12542,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12542,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12542,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12542,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12542,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12542,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12542,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12542,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12542,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12542,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12542,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12542,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12542,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12542,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12542,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12542 : FrameRepair 12542 scalarRow12542 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12542Cells j).1 (repair12542Cells j).2.1
  endpoint_upper := fun j => ((repair12542Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12542Cells j).2.2

theorem repair12543Cells (j : Fin 43) :
    0 ≤ (scalarRow12543.table (sourceIndex j)).upper ∧
    (scalarRow12543.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12543.table (sourceIndex j)).centre) /
      (scalarRow12543.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12543.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12543,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12543,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12543,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12543,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12543,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12543,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12543,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12543,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12543,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12543,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12543,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12543,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12543,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12543,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12543,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12543,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12543,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12543,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12543,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12543,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12543,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12543,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12543,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12543,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12543,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12543,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12543,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12543,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12543,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12543,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12543,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12543,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12543,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12543,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12543,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12543,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12543,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12543,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12543,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12543,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12543,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12543,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12543,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12543,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12543,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12543,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12543,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12543,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12543,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12543,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12543,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12543,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12543,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12543,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12543,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12543,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12543,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12543,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12543,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12543,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12543,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12543,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12543,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12543,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12543,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12543,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12543,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12543,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12543,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12543,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12543,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12543,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12543,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12543,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12543,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12543,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12543,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12543,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12543,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12543,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12543,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12543,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12543,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12543,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12543,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12543,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12543 : FrameRepair 12543 scalarRow12543 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12543Cells j).1 (repair12543Cells j).2.1
  endpoint_upper := fun j => ((repair12543Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12543Cells j).2.2

theorem repair12544Cells (j : Fin 43) :
    0 ≤ (scalarRow12544.table (sourceIndex j)).upper ∧
    (scalarRow12544.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12544.table (sourceIndex j)).centre) /
      (scalarRow12544.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12544.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12544,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12544,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12544,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12544,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12544,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12544,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12544,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12544,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12544,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12544,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12544,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12544,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12544,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12544,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12544,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12544,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12544,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12544,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12544,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12544,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12544,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12544,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12544,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12544,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12544,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12544,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12544,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12544,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12544,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12544,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12544,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12544,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12544,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12544,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12544,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12544,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12544,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12544,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12544,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12544,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12544,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12544,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12544,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12544,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12544,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12544,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12544,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12544,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12544,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12544,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12544,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12544,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12544,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12544,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12544,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12544,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12544,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12544,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12544,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12544,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12544,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12544,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12544,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12544,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12544,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12544,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12544,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12544,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12544,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12544,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12544,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12544,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12544,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12544,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12544,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12544,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12544,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12544,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12544,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12544,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12544,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12544,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12544,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12544,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12544,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12544,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12544 : FrameRepair 12544 scalarRow12544 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12544Cells j).1 (repair12544Cells j).2.1
  endpoint_upper := fun j => ((repair12544Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12544Cells j).2.2

theorem repair12545Cells (j : Fin 43) :
    0 ≤ (scalarRow12545.table (sourceIndex j)).upper ∧
    (scalarRow12545.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12545.table (sourceIndex j)).centre) /
      (scalarRow12545.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12545.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12545,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12545,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12545,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12545,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12545,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12545,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12545,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12545,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12545,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12545,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12545,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12545,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12545,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12545,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12545,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12545,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12545,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12545,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12545,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12545,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12545,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12545,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12545,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12545,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12545,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12545,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12545,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12545,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12545,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12545,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12545,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12545,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12545,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12545,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12545,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12545,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12545,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12545,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12545,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12545,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12545,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12545,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12545,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12545,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12545,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12545,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12545,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12545,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12545,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12545,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12545,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12545,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12545,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12545,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12545,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12545,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12545,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12545,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12545,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12545,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12545,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12545,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12545,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12545,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12545,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12545,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12545,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12545,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12545,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12545,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12545,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12545,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12545,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12545,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12545,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12545,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12545,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12545,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12545,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12545,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12545,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12545,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12545,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12545,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12545,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12545,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12545 : FrameRepair 12545 scalarRow12545 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12545Cells j).1 (repair12545Cells j).2.1
  endpoint_upper := fun j => ((repair12545Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12545Cells j).2.2

theorem repair12546Cells (j : Fin 43) :
    0 ≤ (scalarRow12546.table (sourceIndex j)).upper ∧
    (scalarRow12546.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12546.table (sourceIndex j)).centre) /
      (scalarRow12546.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12546.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12546,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12546,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12546,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12546,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12546,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12546,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12546,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12546,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12546,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12546,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12546,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12546,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12546,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12546,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12546,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12546,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12546,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12546,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12546,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12546,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12546,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12546,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12546,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12546,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12546,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12546,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12546,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12546,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12546,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12546,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12546,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12546,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12546,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12546,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12546,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12546,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12546,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12546,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12546,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12546,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12546,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12546,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12546,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12546,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12546,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12546,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12546,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12546,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12546,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12546,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12546,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12546,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12546,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12546,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12546,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12546,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12546,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12546,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12546,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12546,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12546,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12546,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12546,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12546,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12546,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12546,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12546,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12546,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12546,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12546,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12546,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12546,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12546,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12546,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12546,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12546,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12546,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12546,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12546,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12546,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12546,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12546,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12546,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12546,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12546,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12546,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12546 : FrameRepair 12546 scalarRow12546 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12546Cells j).1 (repair12546Cells j).2.1
  endpoint_upper := fun j => ((repair12546Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12546Cells j).2.2

theorem repair12547Cells (j : Fin 43) :
    0 ≤ (scalarRow12547.table (sourceIndex j)).upper ∧
    (scalarRow12547.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12547.table (sourceIndex j)).centre) /
      (scalarRow12547.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12547.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12547,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12547,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12547,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12547,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12547,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12547,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12547,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12547,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12547,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12547,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12547,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12547,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12547,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12547,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12547,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12547,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12547,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12547,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12547,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12547,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12547,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12547,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12547,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12547,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12547,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12547,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12547,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12547,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12547,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12547,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12547,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12547,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12547,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12547,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12547,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12547,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12547,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12547,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12547,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12547,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12547,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12547,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12547,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12547,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12547,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12547,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12547,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12547,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12547,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12547,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12547,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12547,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12547,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12547,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12547,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12547,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12547,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12547,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12547,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12547,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12547,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12547,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12547,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12547,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12547,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12547,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12547,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12547,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12547,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12547,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12547,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12547,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12547,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12547,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12547,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12547,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12547,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12547,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12547,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12547,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12547,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12547,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12547,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12547,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12547,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12547,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12547 : FrameRepair 12547 scalarRow12547 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12547Cells j).1 (repair12547Cells j).2.1
  endpoint_upper := fun j => ((repair12547Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12547Cells j).2.2

theorem repair12548Cells (j : Fin 43) :
    0 ≤ (scalarRow12548.table (sourceIndex j)).upper ∧
    (scalarRow12548.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12548.table (sourceIndex j)).centre) /
      (scalarRow12548.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12548.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12548,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12548,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12548,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12548,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12548,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12548,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12548,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12548,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12548,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12548,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12548,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12548,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12548,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12548,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12548,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12548,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12548,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12548,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12548,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12548,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12548,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12548,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12548,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12548,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12548,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12548,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12548,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12548,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12548,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12548,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12548,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12548,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12548,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12548,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12548,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12548,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12548,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12548,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12548,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12548,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12548,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12548,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12548,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12548,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12548,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12548,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12548,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12548,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12548,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12548,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12548,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12548,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12548,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12548,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12548,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12548,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12548,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12548,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12548,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12548,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12548,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12548,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12548,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12548,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12548,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12548,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12548,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12548,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12548,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12548,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12548,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12548,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12548,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12548,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12548,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12548,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12548,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12548,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12548,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12548,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12548,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12548,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12548,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12548,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12548,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12548,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12548 : FrameRepair 12548 scalarRow12548 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12548Cells j).1 (repair12548Cells j).2.1
  endpoint_upper := fun j => ((repair12548Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12548Cells j).2.2

theorem repair12549Cells (j : Fin 43) :
    0 ≤ (scalarRow12549.table (sourceIndex j)).upper ∧
    (scalarRow12549.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12549.table (sourceIndex j)).centre) /
      (scalarRow12549.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12549.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12549,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12549,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12549,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12549,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12549,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12549,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12549,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12549,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12549,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12549,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12549,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12549,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12549,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12549,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12549,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12549,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12549,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12549,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12549,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12549,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12549,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12549,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12549,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12549,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12549,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12549,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12549,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12549,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12549,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12549,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12549,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12549,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12549,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12549,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12549,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12549,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12549,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12549,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12549,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12549,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12549,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12549,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12549,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12549,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12549,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12549,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12549,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12549,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12549,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12549,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12549,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12549,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12549,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12549,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12549,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12549,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12549,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12549,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12549,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12549,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12549,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12549,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12549,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12549,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12549,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12549,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12549,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12549,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12549,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12549,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12549,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12549,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12549,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12549,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12549,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12549,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12549,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12549,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12549,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12549,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12549,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12549,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12549,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12549,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12549,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12549,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12549 : FrameRepair 12549 scalarRow12549 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12549Cells j).1 (repair12549Cells j).2.1
  endpoint_upper := fun j => ((repair12549Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12549Cells j).2.2

end BstLean.Part269
