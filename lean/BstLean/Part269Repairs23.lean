import BstLean.Part269Rows23
import BstLean.Part269RepairCommon
namespace BstLean.Part269
open Real Set BstLean.Part255 BstLean.Part263 BstLean.Part264
theorem repair12925Cells (j : Fin 43) :
    0 ≤ (scalarRow12925.table (sourceIndex j)).upper ∧
    (scalarRow12925.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12925.table (sourceIndex j)).centre) /
      (scalarRow12925.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12925.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12925,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12925,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12925,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12925,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12925,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12925,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12925,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12925,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12925,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12925,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12925,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12925,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12925,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12925,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12925,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12925,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12925,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12925,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12925,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12925,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12925,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12925,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12925,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12925,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12925,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12925,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12925,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12925,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12925,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12925,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12925,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12925,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12925,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12925,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12925,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12925,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12925,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12925,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12925,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12925,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12925,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12925,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12925,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12925,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12925,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12925,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12925,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12925,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12925,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12925,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12925,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12925,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12925,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12925,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12925,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12925,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12925,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12925,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12925,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12925,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12925,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12925,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12925,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12925,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12925,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12925,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12925,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12925,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12925,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12925,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12925,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12925,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12925,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12925,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12925,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12925,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12925,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12925,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12925,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12925,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12925,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12925,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12925,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12925,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12925,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12925,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12925 : FrameRepair 12925 scalarRow12925 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12925Cells j).1 (repair12925Cells j).2.1
  endpoint_upper := fun j => ((repair12925Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12925Cells j).2.2

theorem repair12926Cells (j : Fin 43) :
    0 ≤ (scalarRow12926.table (sourceIndex j)).upper ∧
    (scalarRow12926.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12926.table (sourceIndex j)).centre) /
      (scalarRow12926.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12926.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12926,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12926,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12926,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12926,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12926,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12926,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12926,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12926,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12926,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12926,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12926,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12926,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12926,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12926,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12926,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12926,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12926,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12926,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12926,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12926,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12926,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12926,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12926,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12926,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12926,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12926,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12926,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12926,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12926,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12926,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12926,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12926,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12926,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12926,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12926,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12926,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12926,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12926,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12926,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12926,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12926,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12926,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12926,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12926,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12926,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12926,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12926,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12926,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12926,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12926,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12926,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12926,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12926,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12926,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12926,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12926,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12926,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12926,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12926,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12926,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12926,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12926,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12926,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12926,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12926,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12926,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12926,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12926,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12926,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12926,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12926,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12926,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12926,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12926,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12926,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12926,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12926,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12926,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12926,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12926,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12926,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12926,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12926,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12926,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12926,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12926,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12926 : FrameRepair 12926 scalarRow12926 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12926Cells j).1 (repair12926Cells j).2.1
  endpoint_upper := fun j => ((repair12926Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12926Cells j).2.2

theorem repair12927Cells (j : Fin 43) :
    0 ≤ (scalarRow12927.table (sourceIndex j)).upper ∧
    (scalarRow12927.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12927.table (sourceIndex j)).centre) /
      (scalarRow12927.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12927.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12927,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12927,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12927,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12927,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12927,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12927,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12927,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12927,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12927,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12927,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12927,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12927,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12927,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12927,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12927,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12927,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12927,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12927,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12927,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12927,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12927,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12927,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12927,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12927,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12927,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12927,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12927,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12927,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12927,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12927,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12927,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12927,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12927,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12927,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12927,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12927,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12927,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12927,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12927,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12927,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12927,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12927,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12927,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12927,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12927,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12927,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12927,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12927,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12927,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12927,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12927,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12927,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12927,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12927,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12927,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12927,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12927,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12927,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12927,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12927,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12927,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12927,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12927,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12927,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12927,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12927,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12927,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12927,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12927,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12927,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12927,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12927,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12927,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12927,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12927,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12927,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12927,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12927,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12927,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12927,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12927,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12927,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12927,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12927,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12927,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12927,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12927 : FrameRepair 12927 scalarRow12927 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12927Cells j).1 (repair12927Cells j).2.1
  endpoint_upper := fun j => ((repair12927Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12927Cells j).2.2

theorem repair12928Cells (j : Fin 43) :
    0 ≤ (scalarRow12928.table (sourceIndex j)).upper ∧
    (scalarRow12928.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12928.table (sourceIndex j)).centre) /
      (scalarRow12928.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12928.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12928,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12928,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12928,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12928,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12928,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12928,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12928,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12928,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12928,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12928,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12928,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12928,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12928,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12928,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12928,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12928,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12928,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12928,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12928,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12928,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12928,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12928,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12928,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12928,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12928,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12928,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12928,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12928,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12928,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12928,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12928,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12928,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12928,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12928,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12928,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12928,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12928,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12928,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12928,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12928,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12928,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12928,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12928,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12928,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12928,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12928,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12928,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12928,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12928,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12928,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12928,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12928,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12928,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12928,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12928,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12928,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12928,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12928,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12928,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12928,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12928,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12928,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12928,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12928,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12928,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12928,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12928,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12928,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12928,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12928,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12928,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12928,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12928,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12928,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12928,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12928,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12928,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12928,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12928,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12928,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12928,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12928,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12928,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12928,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12928,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12928,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12928 : FrameRepair 12928 scalarRow12928 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12928Cells j).1 (repair12928Cells j).2.1
  endpoint_upper := fun j => ((repair12928Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12928Cells j).2.2

theorem repair12929Cells (j : Fin 43) :
    0 ≤ (scalarRow12929.table (sourceIndex j)).upper ∧
    (scalarRow12929.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12929.table (sourceIndex j)).centre) /
      (scalarRow12929.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12929.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12929,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12929,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12929,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12929,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12929,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12929,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12929,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12929,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12929,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12929,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12929,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12929,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12929,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12929,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12929,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12929,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12929,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12929,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12929,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12929,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12929,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12929,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12929,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12929,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12929,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12929,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12929,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12929,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12929,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12929,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12929,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12929,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12929,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12929,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12929,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12929,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12929,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12929,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12929,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12929,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12929,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12929,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12929,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12929,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12929,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12929,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12929,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12929,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12929,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12929,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12929,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12929,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12929,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12929,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12929,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12929,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12929,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12929,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12929,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12929,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12929,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12929,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12929,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12929,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12929,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12929,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12929,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12929,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12929,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12929,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12929,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12929,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12929,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12929,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12929,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12929,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12929,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12929,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12929,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12929,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12929,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12929,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12929,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12929,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12929,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12929,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12929 : FrameRepair 12929 scalarRow12929 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12929Cells j).1 (repair12929Cells j).2.1
  endpoint_upper := fun j => ((repair12929Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12929Cells j).2.2

theorem repair12930Cells (j : Fin 43) :
    0 ≤ (scalarRow12930.table (sourceIndex j)).upper ∧
    (scalarRow12930.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12930.table (sourceIndex j)).centre) /
      (scalarRow12930.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12930.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12930,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12930,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12930,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12930,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12930,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12930,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12930,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12930,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12930,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12930,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12930,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12930,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12930,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12930,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12930,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12930,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12930,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12930,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12930,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12930,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12930,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12930,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12930,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12930,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12930,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12930,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12930,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12930,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12930,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12930,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12930,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12930,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12930,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12930,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12930,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12930,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12930,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12930,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12930,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12930,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12930,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12930,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12930,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12930,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12930,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12930,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12930,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12930,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12930,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12930,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12930,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12930,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12930,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12930,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12930,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12930,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12930,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12930,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12930,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12930,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12930,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12930,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12930,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12930,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12930,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12930,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12930,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12930,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12930,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12930,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12930,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12930,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12930,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12930,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12930,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12930,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12930,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12930,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12930,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12930,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12930,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12930,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12930,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12930,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12930,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12930,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12930 : FrameRepair 12930 scalarRow12930 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12930Cells j).1 (repair12930Cells j).2.1
  endpoint_upper := fun j => ((repair12930Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12930Cells j).2.2

theorem repair12931Cells (j : Fin 43) :
    0 ≤ (scalarRow12931.table (sourceIndex j)).upper ∧
    (scalarRow12931.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12931.table (sourceIndex j)).centre) /
      (scalarRow12931.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12931.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12931,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12931,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12931,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12931,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12931,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12931,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12931,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12931,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12931,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12931,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12931,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12931,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12931,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12931,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12931,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12931,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12931,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12931,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12931,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12931,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12931,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12931,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12931,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12931,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12931,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12931,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12931,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12931,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12931,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12931,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12931,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12931,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12931,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12931,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12931,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12931,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12931,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12931,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12931,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12931,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12931,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12931,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12931,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12931,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12931,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12931,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12931,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12931,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12931,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12931,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12931,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12931,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12931,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12931,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12931,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12931,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12931,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12931,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12931,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12931,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12931,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12931,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12931,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12931,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12931,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12931,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12931,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12931,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12931,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12931,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12931,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12931,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12931,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12931,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12931,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12931,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12931,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12931,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12931,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12931,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12931,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12931,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12931,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12931,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12931,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12931,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12931 : FrameRepair 12931 scalarRow12931 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12931Cells j).1 (repair12931Cells j).2.1
  endpoint_upper := fun j => ((repair12931Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12931Cells j).2.2

theorem repair12932Cells (j : Fin 43) :
    0 ≤ (scalarRow12932.table (sourceIndex j)).upper ∧
    (scalarRow12932.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12932.table (sourceIndex j)).centre) /
      (scalarRow12932.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12932.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12932,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12932,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12932,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12932,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12932,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12932,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12932,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12932,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12932,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12932,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12932,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12932,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12932,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12932,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12932,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12932,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12932,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12932,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12932,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12932,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12932,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12932,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12932,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12932,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12932,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12932,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12932,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12932,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12932,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12932,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12932,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12932,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12932,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12932,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12932,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12932,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12932,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12932,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12932,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12932,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12932,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12932,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12932,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12932,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12932,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12932,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12932,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12932,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12932,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12932,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12932,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12932,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12932,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12932,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12932,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12932,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12932,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12932,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12932,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12932,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12932,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12932,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12932,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12932,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12932,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12932,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12932,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12932,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12932,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12932,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12932,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12932,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12932,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12932,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12932,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12932,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12932,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12932,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12932,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12932,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12932,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12932,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12932,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12932,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12932,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12932,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12932 : FrameRepair 12932 scalarRow12932 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12932Cells j).1 (repair12932Cells j).2.1
  endpoint_upper := fun j => ((repair12932Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12932Cells j).2.2

theorem repair12933Cells (j : Fin 43) :
    0 ≤ (scalarRow12933.table (sourceIndex j)).upper ∧
    (scalarRow12933.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12933.table (sourceIndex j)).centre) /
      (scalarRow12933.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12933.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12933,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12933,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12933,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12933,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12933,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12933,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12933,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12933,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12933,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12933,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12933,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12933,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12933,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12933,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12933,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12933,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12933,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12933,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12933,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12933,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12933,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12933,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12933,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12933,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12933,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12933,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12933,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12933,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12933,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12933,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12933,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12933,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12933,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12933,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12933,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12933,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12933,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12933,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12933,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12933,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12933,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12933,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12933,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12933,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12933,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12933,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12933,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12933,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12933,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12933,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12933,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12933,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12933,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12933,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12933,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12933,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12933,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12933,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12933,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12933,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12933,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12933,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12933,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12933,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12933,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12933,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12933,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12933,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12933,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12933,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12933,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12933,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12933,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12933,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12933,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12933,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12933,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12933,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12933,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12933,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12933,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12933,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12933,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12933,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12933,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12933,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12933 : FrameRepair 12933 scalarRow12933 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12933Cells j).1 (repair12933Cells j).2.1
  endpoint_upper := fun j => ((repair12933Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12933Cells j).2.2

theorem repair12934Cells (j : Fin 43) :
    0 ≤ (scalarRow12934.table (sourceIndex j)).upper ∧
    (scalarRow12934.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12934.table (sourceIndex j)).centre) /
      (scalarRow12934.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12934.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12934,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12934,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12934,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12934,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12934,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12934,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12934,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12934,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12934,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12934,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12934,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12934,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12934,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12934,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12934,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12934,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12934,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12934,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12934,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12934,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12934,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12934,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12934,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12934,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12934,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12934,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12934,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12934,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12934,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12934,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12934,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12934,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12934,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12934,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12934,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12934,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12934,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12934,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12934,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12934,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12934,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12934,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12934,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12934,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12934,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12934,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12934,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12934,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12934,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12934,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12934,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12934,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12934,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12934,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12934,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12934,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12934,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12934,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12934,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12934,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12934,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12934,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12934,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12934,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12934,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12934,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12934,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12934,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12934,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12934,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12934,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12934,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12934,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12934,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12934,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12934,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12934,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12934,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12934,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12934,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12934,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12934,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12934,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12934,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12934,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12934,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12934 : FrameRepair 12934 scalarRow12934 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12934Cells j).1 (repair12934Cells j).2.1
  endpoint_upper := fun j => ((repair12934Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12934Cells j).2.2

theorem repair12935Cells (j : Fin 43) :
    0 ≤ (scalarRow12935.table (sourceIndex j)).upper ∧
    (scalarRow12935.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12935.table (sourceIndex j)).centre) /
      (scalarRow12935.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12935.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12935,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12935,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12935,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12935,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12935,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12935,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12935,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12935,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12935,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12935,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12935,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12935,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12935,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12935,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12935,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12935,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12935,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12935,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12935,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12935,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12935,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12935,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12935,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12935,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12935,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12935,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12935,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12935,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12935,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12935,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12935,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12935,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12935,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12935,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12935,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12935,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12935,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12935,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12935,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12935,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12935,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12935,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12935,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12935,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12935,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12935,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12935,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12935,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12935,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12935,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12935,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12935,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12935,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12935,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12935,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12935,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12935,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12935,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12935,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12935,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12935,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12935,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12935,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12935,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12935,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12935,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12935,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12935,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12935,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12935,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12935,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12935,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12935,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12935,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12935,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12935,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12935,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12935,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12935,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12935,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12935,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12935,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12935,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12935,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12935,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12935,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12935 : FrameRepair 12935 scalarRow12935 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12935Cells j).1 (repair12935Cells j).2.1
  endpoint_upper := fun j => ((repair12935Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12935Cells j).2.2

theorem repair12936Cells (j : Fin 43) :
    0 ≤ (scalarRow12936.table (sourceIndex j)).upper ∧
    (scalarRow12936.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12936.table (sourceIndex j)).centre) /
      (scalarRow12936.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12936.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12936,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12936,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12936,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12936,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12936,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12936,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12936,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12936,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12936,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12936,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12936,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12936,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12936,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12936,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12936,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12936,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12936,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12936,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12936,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12936,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12936,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12936,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12936,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12936,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12936,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12936,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12936,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12936,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12936,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12936,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12936,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12936,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12936,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12936,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12936,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12936,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12936,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12936,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12936,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12936,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12936,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12936,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12936,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12936,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12936,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12936,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12936,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12936,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12936,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12936,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12936,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12936,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12936,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12936,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12936,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12936,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12936,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12936,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12936,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12936,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12936,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12936,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12936,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12936,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12936,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12936,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12936,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12936,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12936,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12936,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12936,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12936,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12936,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12936,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12936,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12936,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12936,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12936,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12936,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12936,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12936,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12936,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12936,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12936,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12936,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12936,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12936 : FrameRepair 12936 scalarRow12936 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12936Cells j).1 (repair12936Cells j).2.1
  endpoint_upper := fun j => ((repair12936Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12936Cells j).2.2

theorem repair12937Cells (j : Fin 43) :
    0 ≤ (scalarRow12937.table (sourceIndex j)).upper ∧
    (scalarRow12937.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12937.table (sourceIndex j)).centre) /
      (scalarRow12937.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12937.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12937,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12937,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12937,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12937,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12937,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12937,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12937,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12937,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12937,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12937,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12937,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12937,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12937,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12937,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12937,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12937,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12937,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12937,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12937,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12937,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12937,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12937,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12937,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12937,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12937,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12937,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12937,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12937,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12937,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12937,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12937,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12937,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12937,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12937,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12937,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12937,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12937,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12937,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12937,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12937,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12937,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12937,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12937,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12937,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12937,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12937,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12937,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12937,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12937,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12937,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12937,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12937,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12937,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12937,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12937,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12937,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12937,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12937,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12937,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12937,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12937,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12937,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12937,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12937,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12937,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12937,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12937,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12937,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12937,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12937,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12937,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12937,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12937,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12937,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12937,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12937,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12937,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12937,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12937,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12937,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12937,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12937,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12937,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12937,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12937,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12937,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12937 : FrameRepair 12937 scalarRow12937 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12937Cells j).1 (repair12937Cells j).2.1
  endpoint_upper := fun j => ((repair12937Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12937Cells j).2.2

theorem repair12938Cells (j : Fin 43) :
    0 ≤ (scalarRow12938.table (sourceIndex j)).upper ∧
    (scalarRow12938.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12938.table (sourceIndex j)).centre) /
      (scalarRow12938.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12938.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12938,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12938,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12938,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12938,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12938,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12938,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12938,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12938,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12938,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12938,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12938,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12938,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12938,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12938,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12938,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12938,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12938,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12938,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12938,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12938,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12938,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12938,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12938,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12938,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12938,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12938,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12938,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12938,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12938,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12938,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12938,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12938,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12938,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12938,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12938,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12938,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12938,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12938,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12938,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12938,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12938,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12938,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12938,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12938,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12938,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12938,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12938,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12938,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12938,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12938,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12938,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12938,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12938,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12938,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12938,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12938,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12938,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12938,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12938,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12938,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12938,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12938,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12938,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12938,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12938,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12938,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12938,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12938,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12938,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12938,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12938,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12938,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12938,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12938,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12938,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12938,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12938,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12938,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12938,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12938,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12938,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12938,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12938,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12938,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12938,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12938,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12938 : FrameRepair 12938 scalarRow12938 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12938Cells j).1 (repair12938Cells j).2.1
  endpoint_upper := fun j => ((repair12938Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12938Cells j).2.2

theorem repair12939Cells (j : Fin 43) :
    0 ≤ (scalarRow12939.table (sourceIndex j)).upper ∧
    (scalarRow12939.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12939.table (sourceIndex j)).centre) /
      (scalarRow12939.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12939.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12939,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12939,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12939,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12939,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12939,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12939,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12939,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12939,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12939,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12939,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12939,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12939,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12939,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12939,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12939,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12939,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12939,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12939,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12939,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12939,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12939,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12939,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12939,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12939,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12939,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12939,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12939,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12939,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12939,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12939,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12939,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12939,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12939,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12939,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12939,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12939,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12939,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12939,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12939,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12939,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12939,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12939,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12939,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12939,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12939,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12939,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12939,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12939,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12939,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12939,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12939,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12939,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12939,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12939,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12939,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12939,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12939,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12939,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12939,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12939,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12939,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12939,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12939,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12939,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12939,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12939,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12939,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12939,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12939,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12939,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12939,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12939,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12939,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12939,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12939,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12939,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12939,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12939,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12939,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12939,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12939,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12939,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12939,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12939,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12939,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12939,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12939 : FrameRepair 12939 scalarRow12939 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12939Cells j).1 (repair12939Cells j).2.1
  endpoint_upper := fun j => ((repair12939Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12939Cells j).2.2

theorem repair12940Cells (j : Fin 43) :
    0 ≤ (scalarRow12940.table (sourceIndex j)).upper ∧
    (scalarRow12940.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12940.table (sourceIndex j)).centre) /
      (scalarRow12940.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12940.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12940,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12940,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12940,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12940,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12940,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12940,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12940,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12940,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12940,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12940,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12940,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12940,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12940,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12940,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12940,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12940,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12940,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12940,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12940,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12940,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12940,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12940,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12940,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12940,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12940,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12940,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12940,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12940,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12940,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12940,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12940,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12940,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12940,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12940,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12940,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12940,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12940,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12940,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12940,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12940,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12940,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12940,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12940,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12940,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12940,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12940,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12940,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12940,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12940,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12940,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12940,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12940,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12940,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12940,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12940,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12940,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12940,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12940,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12940,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12940,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12940,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12940,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12940,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12940,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12940,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12940,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12940,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12940,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12940,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12940,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12940,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12940,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12940,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12940,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12940,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12940,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12940,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12940,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12940,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12940,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12940,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12940,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12940,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12940,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12940,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12940,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12940 : FrameRepair 12940 scalarRow12940 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12940Cells j).1 (repair12940Cells j).2.1
  endpoint_upper := fun j => ((repair12940Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12940Cells j).2.2

theorem repair12941Cells (j : Fin 43) :
    0 ≤ (scalarRow12941.table (sourceIndex j)).upper ∧
    (scalarRow12941.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12941.table (sourceIndex j)).centre) /
      (scalarRow12941.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12941.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12941,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12941,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12941,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12941,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12941,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12941,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12941,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12941,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12941,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12941,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12941,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12941,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12941,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12941,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12941,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12941,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12941,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12941,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12941,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12941,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12941,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12941,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12941,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12941,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12941,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12941,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12941,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12941,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12941,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12941,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12941,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12941,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12941,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12941,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12941,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12941,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12941,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12941,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12941,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12941,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12941,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12941,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12941,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12941,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12941,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12941,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12941,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12941,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12941,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12941,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12941,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12941,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12941,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12941,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12941,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12941,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12941,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12941,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12941,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12941,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12941,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12941,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12941,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12941,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12941,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12941,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12941,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12941,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12941,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12941,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12941,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12941,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12941,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12941,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12941,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12941,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12941,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12941,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12941,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12941,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12941,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12941,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12941,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12941,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12941,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12941,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12941 : FrameRepair 12941 scalarRow12941 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12941Cells j).1 (repair12941Cells j).2.1
  endpoint_upper := fun j => ((repair12941Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12941Cells j).2.2

theorem repair12942Cells (j : Fin 43) :
    0 ≤ (scalarRow12942.table (sourceIndex j)).upper ∧
    (scalarRow12942.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12942.table (sourceIndex j)).centre) /
      (scalarRow12942.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12942.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12942,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12942,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12942,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12942,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12942,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12942,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12942,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12942,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12942,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12942,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12942,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12942,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12942,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12942,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12942,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12942,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12942,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12942,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12942,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12942,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12942,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12942,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12942,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12942,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12942,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12942,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12942,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12942,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12942,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12942,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12942,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12942,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12942,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12942,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12942,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12942,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12942,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12942,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12942,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12942,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12942,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12942,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12942,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12942,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12942,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12942,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12942,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12942,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12942,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12942,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12942,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12942,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12942,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12942,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12942,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12942,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12942,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12942,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12942,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12942,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12942,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12942,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12942,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12942,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12942,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12942,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12942,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12942,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12942,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12942,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12942,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12942,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12942,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12942,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12942,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12942,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12942,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12942,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12942,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12942,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12942,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12942,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12942,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12942,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12942,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12942,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12942 : FrameRepair 12942 scalarRow12942 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12942Cells j).1 (repair12942Cells j).2.1
  endpoint_upper := fun j => ((repair12942Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12942Cells j).2.2

theorem repair12943Cells (j : Fin 43) :
    0 ≤ (scalarRow12943.table (sourceIndex j)).upper ∧
    (scalarRow12943.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12943.table (sourceIndex j)).centre) /
      (scalarRow12943.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12943.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12943,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12943,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12943,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12943,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12943,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12943,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12943,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12943,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12943,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12943,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12943,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12943,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12943,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12943,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12943,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12943,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12943,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12943,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12943,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12943,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12943,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12943,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12943,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12943,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12943,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12943,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12943,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12943,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12943,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12943,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12943,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12943,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12943,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12943,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12943,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12943,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12943,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12943,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12943,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12943,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12943,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12943,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12943,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12943,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12943,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12943,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12943,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12943,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12943,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12943,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12943,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12943,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12943,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12943,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12943,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12943,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12943,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12943,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12943,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12943,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12943,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12943,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12943,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12943,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12943,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12943,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12943,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12943,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12943,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12943,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12943,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12943,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12943,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12943,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12943,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12943,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12943,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12943,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12943,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12943,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12943,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12943,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12943,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12943,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12943,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12943,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12943 : FrameRepair 12943 scalarRow12943 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12943Cells j).1 (repair12943Cells j).2.1
  endpoint_upper := fun j => ((repair12943Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12943Cells j).2.2

theorem repair12944Cells (j : Fin 43) :
    0 ≤ (scalarRow12944.table (sourceIndex j)).upper ∧
    (scalarRow12944.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12944.table (sourceIndex j)).centre) /
      (scalarRow12944.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12944.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12944,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12944,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12944,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12944,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12944,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12944,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12944,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12944,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12944,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12944,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12944,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12944,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12944,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12944,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12944,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12944,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12944,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12944,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12944,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12944,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12944,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12944,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12944,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12944,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12944,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12944,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12944,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12944,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12944,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12944,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12944,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12944,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12944,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12944,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12944,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12944,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12944,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12944,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12944,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12944,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12944,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12944,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12944,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12944,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12944,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12944,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12944,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12944,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12944,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12944,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12944,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12944,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12944,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12944,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12944,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12944,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12944,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12944,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12944,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12944,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12944,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12944,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12944,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12944,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12944,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12944,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12944,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12944,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12944,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12944,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12944,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12944,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12944,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12944,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12944,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12944,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12944,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12944,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12944,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12944,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12944,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12944,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12944,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12944,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12944,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12944,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12944 : FrameRepair 12944 scalarRow12944 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12944Cells j).1 (repair12944Cells j).2.1
  endpoint_upper := fun j => ((repair12944Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12944Cells j).2.2

theorem repair12945Cells (j : Fin 43) :
    0 ≤ (scalarRow12945.table (sourceIndex j)).upper ∧
    (scalarRow12945.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12945.table (sourceIndex j)).centre) /
      (scalarRow12945.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12945.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12945,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12945,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12945,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12945,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12945,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12945,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12945,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12945,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12945,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12945,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12945,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12945,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12945,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12945,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12945,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12945,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12945,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12945,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12945,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12945,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12945,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12945,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12945,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12945,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12945,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12945,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12945,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12945,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12945,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12945,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12945,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12945,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12945,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12945,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12945,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12945,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12945,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12945,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12945,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12945,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12945,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12945,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12945,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12945,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12945,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12945,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12945,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12945,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12945,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12945,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12945,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12945,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12945,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12945,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12945,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12945,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12945,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12945,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12945,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12945,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12945,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12945,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12945,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12945,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12945,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12945,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12945,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12945,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12945,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12945,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12945,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12945,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12945,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12945,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12945,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12945,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12945,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12945,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12945,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12945,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12945,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12945,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12945,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12945,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12945,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12945,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12945 : FrameRepair 12945 scalarRow12945 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12945Cells j).1 (repair12945Cells j).2.1
  endpoint_upper := fun j => ((repair12945Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12945Cells j).2.2

theorem repair12946Cells (j : Fin 43) :
    0 ≤ (scalarRow12946.table (sourceIndex j)).upper ∧
    (scalarRow12946.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12946.table (sourceIndex j)).centre) /
      (scalarRow12946.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12946.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12946,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12946,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12946,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12946,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12946,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12946,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12946,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12946,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12946,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12946,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12946,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12946,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12946,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12946,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12946,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12946,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12946,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12946,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12946,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12946,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12946,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12946,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12946,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12946,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12946,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12946,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12946,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12946,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12946,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12946,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12946,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12946,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12946,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12946,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12946,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12946,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12946,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12946,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12946,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12946,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12946,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12946,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12946,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12946,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12946,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12946,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12946,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12946,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12946,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12946,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12946,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12946,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12946,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12946,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12946,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12946,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12946,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12946,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12946,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12946,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12946,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12946,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12946,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12946,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12946,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12946,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12946,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12946,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12946,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12946,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12946,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12946,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12946,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12946,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12946,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12946,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12946,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12946,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12946,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12946,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12946,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12946,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12946,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12946,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12946,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12946,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12946 : FrameRepair 12946 scalarRow12946 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12946Cells j).1 (repair12946Cells j).2.1
  endpoint_upper := fun j => ((repair12946Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12946Cells j).2.2

theorem repair12947Cells (j : Fin 43) :
    0 ≤ (scalarRow12947.table (sourceIndex j)).upper ∧
    (scalarRow12947.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12947.table (sourceIndex j)).centre) /
      (scalarRow12947.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12947.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12947,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12947,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12947,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12947,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12947,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12947,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12947,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12947,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12947,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12947,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12947,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12947,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12947,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12947,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12947,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12947,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12947,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12947,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12947,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12947,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12947,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12947,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12947,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12947,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12947,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12947,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12947,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12947,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12947,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12947,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12947,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12947,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12947,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12947,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12947,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12947,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12947,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12947,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12947,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12947,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12947,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12947,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12947,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12947,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12947,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12947,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12947,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12947,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12947,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12947,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12947,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12947,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12947,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12947,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12947,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12947,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12947,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12947,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12947,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12947,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12947,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12947,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12947,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12947,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12947,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12947,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12947,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12947,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12947,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12947,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12947,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12947,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12947,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12947,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12947,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12947,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12947,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12947,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12947,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12947,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12947,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12947,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12947,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12947,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12947,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12947,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12947 : FrameRepair 12947 scalarRow12947 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12947Cells j).1 (repair12947Cells j).2.1
  endpoint_upper := fun j => ((repair12947Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12947Cells j).2.2

theorem repair12948Cells (j : Fin 43) :
    0 ≤ (scalarRow12948.table (sourceIndex j)).upper ∧
    (scalarRow12948.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12948.table (sourceIndex j)).centre) /
      (scalarRow12948.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12948.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12948,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12948,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12948,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12948,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12948,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12948,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12948,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12948,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12948,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12948,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12948,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12948,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12948,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12948,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12948,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12948,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12948,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12948,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12948,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12948,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12948,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12948,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12948,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12948,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12948,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12948,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12948,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12948,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12948,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12948,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12948,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12948,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12948,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12948,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12948,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12948,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12948,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12948,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12948,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12948,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12948,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12948,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12948,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12948,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12948,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12948,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12948,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12948,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12948,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12948,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12948,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12948,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12948,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12948,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12948,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12948,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12948,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12948,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12948,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12948,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12948,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12948,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12948,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12948,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12948,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12948,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12948,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12948,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12948,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12948,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12948,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12948,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12948,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12948,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12948,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12948,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12948,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12948,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12948,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12948,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12948,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12948,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12948,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12948,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12948,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12948,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12948 : FrameRepair 12948 scalarRow12948 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12948Cells j).1 (repair12948Cells j).2.1
  endpoint_upper := fun j => ((repair12948Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12948Cells j).2.2

theorem repair12949Cells (j : Fin 43) :
    0 ≤ (scalarRow12949.table (sourceIndex j)).upper ∧
    (scalarRow12949.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12949.table (sourceIndex j)).centre) /
      (scalarRow12949.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12949.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12949,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12949,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12949,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12949,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12949,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12949,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12949,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12949,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12949,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12949,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12949,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12949,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12949,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12949,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12949,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12949,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12949,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12949,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12949,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12949,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12949,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12949,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12949,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12949,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12949,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12949,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12949,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12949,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12949,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12949,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12949,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12949,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12949,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12949,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12949,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12949,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12949,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12949,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12949,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12949,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12949,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12949,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12949,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12949,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12949,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12949,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12949,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12949,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12949,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12949,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12949,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12949,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12949,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12949,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12949,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12949,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12949,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12949,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12949,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12949,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12949,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12949,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12949,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12949,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12949,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12949,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12949,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12949,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12949,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12949,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12949,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12949,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12949,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12949,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12949,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12949,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12949,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12949,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12949,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12949,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12949,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12949,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12949,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12949,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12949,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12949,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12949 : FrameRepair 12949 scalarRow12949 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12949Cells j).1 (repair12949Cells j).2.1
  endpoint_upper := fun j => ((repair12949Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12949Cells j).2.2

end BstLean.Part269
