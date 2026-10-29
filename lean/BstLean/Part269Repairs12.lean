import BstLean.Part269Rows12
import BstLean.Part269RepairCommon
namespace BstLean.Part269
open Real Set BstLean.Part255 BstLean.Part263 BstLean.Part264
theorem repair12650Cells (j : Fin 43) :
    0 ≤ (scalarRow12650.table (sourceIndex j)).upper ∧
    (scalarRow12650.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12650.table (sourceIndex j)).centre) /
      (scalarRow12650.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12650.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12650,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12650,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12650,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12650,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12650,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12650,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12650,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12650,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12650,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12650,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12650,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12650,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12650,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12650,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12650,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12650,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12650,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12650,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12650,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12650,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12650,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12650,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12650,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12650,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12650,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12650,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12650,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12650,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12650,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12650,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12650,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12650,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12650,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12650,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12650,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12650,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12650,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12650,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12650,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12650,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12650,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12650,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12650,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12650,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12650,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12650,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12650,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12650,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12650,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12650,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12650,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12650,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12650,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12650,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12650,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12650,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12650,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12650,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12650,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12650,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12650,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12650,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12650,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12650,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12650,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12650,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12650,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12650,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12650,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12650,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12650,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12650,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12650,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12650,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12650,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12650,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12650,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12650,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12650,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12650,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12650,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12650,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12650,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12650,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12650,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12650,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12650 : FrameRepair 12650 scalarRow12650 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12650Cells j).1 (repair12650Cells j).2.1
  endpoint_upper := fun j => ((repair12650Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12650Cells j).2.2

theorem repair12651Cells (j : Fin 43) :
    0 ≤ (scalarRow12651.table (sourceIndex j)).upper ∧
    (scalarRow12651.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12651.table (sourceIndex j)).centre) /
      (scalarRow12651.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12651.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12651,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12651,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12651,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12651,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12651,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12651,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12651,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12651,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12651,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12651,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12651,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12651,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12651,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12651,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12651,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12651,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12651,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12651,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12651,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12651,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12651,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12651,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12651,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12651,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12651,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12651,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12651,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12651,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12651,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12651,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12651,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12651,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12651,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12651,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12651,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12651,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12651,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12651,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12651,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12651,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12651,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12651,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12651,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12651,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12651,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12651,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12651,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12651,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12651,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12651,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12651,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12651,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12651,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12651,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12651,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12651,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12651,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12651,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12651,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12651,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12651,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12651,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12651,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12651,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12651,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12651,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12651,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12651,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12651,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12651,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12651,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12651,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12651,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12651,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12651,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12651,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12651,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12651,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12651,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12651,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12651,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12651,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12651,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12651,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12651,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12651,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12651 : FrameRepair 12651 scalarRow12651 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12651Cells j).1 (repair12651Cells j).2.1
  endpoint_upper := fun j => ((repair12651Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12651Cells j).2.2

theorem repair12652Cells (j : Fin 43) :
    0 ≤ (scalarRow12652.table (sourceIndex j)).upper ∧
    (scalarRow12652.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12652.table (sourceIndex j)).centre) /
      (scalarRow12652.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12652.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12652,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12652,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12652,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12652,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12652,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12652,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12652,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12652,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12652,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12652,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12652,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12652,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12652,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12652,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12652,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12652,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12652,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12652,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12652,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12652,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12652,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12652,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12652,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12652,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12652,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12652,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12652,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12652,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12652,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12652,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12652,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12652,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12652,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12652,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12652,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12652,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12652,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12652,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12652,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12652,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12652,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12652,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12652,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12652,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12652,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12652,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12652,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12652,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12652,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12652,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12652,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12652,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12652,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12652,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12652,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12652,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12652,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12652,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12652,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12652,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12652,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12652,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12652,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12652,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12652,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12652,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12652,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12652,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12652,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12652,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12652,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12652,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12652,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12652,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12652,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12652,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12652,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12652,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12652,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12652,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12652,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12652,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12652,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12652,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12652,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12652,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12652 : FrameRepair 12652 scalarRow12652 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12652Cells j).1 (repair12652Cells j).2.1
  endpoint_upper := fun j => ((repair12652Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12652Cells j).2.2

theorem repair12653Cells (j : Fin 43) :
    0 ≤ (scalarRow12653.table (sourceIndex j)).upper ∧
    (scalarRow12653.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12653.table (sourceIndex j)).centre) /
      (scalarRow12653.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12653.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12653,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12653,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12653,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12653,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12653,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12653,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12653,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12653,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12653,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12653,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12653,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12653,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12653,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12653,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12653,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12653,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12653,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12653,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12653,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12653,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12653,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12653,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12653,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12653,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12653,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12653,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12653,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12653,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12653,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12653,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12653,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12653,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12653,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12653,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12653,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12653,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12653,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12653,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12653,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12653,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12653,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12653,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12653,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12653,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12653,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12653,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12653,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12653,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12653,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12653,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12653,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12653,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12653,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12653,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12653,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12653,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12653,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12653,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12653,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12653,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12653,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12653,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12653,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12653,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12653,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12653,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12653,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12653,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12653,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12653,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12653,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12653,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12653,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12653,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12653,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12653,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12653,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12653,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12653,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12653,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12653,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12653,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12653,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12653,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12653,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12653,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12653 : FrameRepair 12653 scalarRow12653 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12653Cells j).1 (repair12653Cells j).2.1
  endpoint_upper := fun j => ((repair12653Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12653Cells j).2.2

theorem repair12654Cells (j : Fin 43) :
    0 ≤ (scalarRow12654.table (sourceIndex j)).upper ∧
    (scalarRow12654.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12654.table (sourceIndex j)).centre) /
      (scalarRow12654.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12654.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12654,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12654,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12654,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12654,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12654,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12654,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12654,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12654,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12654,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12654,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12654,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12654,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12654,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12654,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12654,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12654,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12654,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12654,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12654,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12654,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12654,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12654,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12654,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12654,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12654,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12654,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12654,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12654,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12654,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12654,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12654,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12654,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12654,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12654,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12654,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12654,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12654,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12654,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12654,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12654,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12654,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12654,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12654,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12654,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12654,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12654,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12654,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12654,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12654,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12654,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12654,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12654,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12654,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12654,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12654,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12654,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12654,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12654,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12654,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12654,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12654,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12654,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12654,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12654,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12654,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12654,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12654,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12654,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12654,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12654,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12654,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12654,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12654,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12654,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12654,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12654,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12654,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12654,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12654,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12654,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12654,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12654,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12654,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12654,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12654,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12654,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12654 : FrameRepair 12654 scalarRow12654 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12654Cells j).1 (repair12654Cells j).2.1
  endpoint_upper := fun j => ((repair12654Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12654Cells j).2.2

theorem repair12655Cells (j : Fin 43) :
    0 ≤ (scalarRow12655.table (sourceIndex j)).upper ∧
    (scalarRow12655.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12655.table (sourceIndex j)).centre) /
      (scalarRow12655.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12655.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12655,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12655,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12655,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12655,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12655,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12655,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12655,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12655,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12655,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12655,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12655,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12655,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12655,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12655,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12655,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12655,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12655,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12655,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12655,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12655,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12655,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12655,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12655,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12655,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12655,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12655,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12655,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12655,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12655,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12655,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12655,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12655,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12655,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12655,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12655,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12655,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12655,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12655,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12655,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12655,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12655,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12655,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12655,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12655,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12655,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12655,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12655,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12655,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12655,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12655,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12655,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12655,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12655,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12655,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12655,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12655,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12655,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12655,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12655,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12655,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12655,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12655,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12655,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12655,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12655,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12655,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12655,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12655,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12655,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12655,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12655,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12655,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12655,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12655,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12655,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12655,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12655,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12655,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12655,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12655,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12655,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12655,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12655,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12655,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12655,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12655,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12655 : FrameRepair 12655 scalarRow12655 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12655Cells j).1 (repair12655Cells j).2.1
  endpoint_upper := fun j => ((repair12655Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12655Cells j).2.2

theorem repair12656Cells (j : Fin 43) :
    0 ≤ (scalarRow12656.table (sourceIndex j)).upper ∧
    (scalarRow12656.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12656.table (sourceIndex j)).centre) /
      (scalarRow12656.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12656.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12656,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12656,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12656,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12656,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12656,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12656,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12656,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12656,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12656,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12656,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12656,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12656,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12656,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12656,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12656,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12656,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12656,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12656,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12656,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12656,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12656,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12656,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12656,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12656,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12656,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12656,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12656,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12656,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12656,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12656,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12656,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12656,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12656,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12656,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12656,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12656,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12656,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12656,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12656,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12656,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12656,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12656,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12656,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12656,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12656,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12656,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12656,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12656,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12656,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12656,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12656,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12656,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12656,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12656,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12656,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12656,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12656,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12656,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12656,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12656,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12656,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12656,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12656,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12656,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12656,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12656,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12656,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12656,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12656,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12656,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12656,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12656,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12656,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12656,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12656,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12656,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12656,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12656,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12656,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12656,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12656,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12656,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12656,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12656,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12656,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12656,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12656 : FrameRepair 12656 scalarRow12656 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12656Cells j).1 (repair12656Cells j).2.1
  endpoint_upper := fun j => ((repair12656Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12656Cells j).2.2

theorem repair12657Cells (j : Fin 43) :
    0 ≤ (scalarRow12657.table (sourceIndex j)).upper ∧
    (scalarRow12657.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12657.table (sourceIndex j)).centre) /
      (scalarRow12657.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12657.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12657,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12657,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12657,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12657,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12657,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12657,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12657,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12657,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12657,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12657,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12657,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12657,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12657,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12657,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12657,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12657,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12657,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12657,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12657,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12657,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12657,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12657,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12657,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12657,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12657,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12657,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12657,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12657,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12657,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12657,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12657,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12657,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12657,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12657,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12657,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12657,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12657,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12657,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12657,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12657,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12657,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12657,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12657,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12657,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12657,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12657,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12657,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12657,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12657,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12657,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12657,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12657,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12657,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12657,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12657,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12657,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12657,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12657,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12657,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12657,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12657,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12657,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12657,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12657,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12657,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12657,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12657,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12657,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12657,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12657,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12657,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12657,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12657,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12657,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12657,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12657,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12657,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12657,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12657,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12657,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12657,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12657,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12657,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12657,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12657,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12657,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12657 : FrameRepair 12657 scalarRow12657 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12657Cells j).1 (repair12657Cells j).2.1
  endpoint_upper := fun j => ((repair12657Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12657Cells j).2.2

theorem repair12658Cells (j : Fin 43) :
    0 ≤ (scalarRow12658.table (sourceIndex j)).upper ∧
    (scalarRow12658.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12658.table (sourceIndex j)).centre) /
      (scalarRow12658.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12658.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12658,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12658,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12658,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12658,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12658,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12658,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12658,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12658,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12658,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12658,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12658,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12658,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12658,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12658,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12658,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12658,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12658,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12658,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12658,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12658,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12658,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12658,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12658,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12658,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12658,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12658,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12658,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12658,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12658,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12658,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12658,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12658,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12658,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12658,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12658,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12658,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12658,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12658,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12658,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12658,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12658,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12658,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12658,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12658,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12658,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12658,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12658,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12658,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12658,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12658,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12658,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12658,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12658,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12658,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12658,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12658,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12658,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12658,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12658,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12658,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12658,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12658,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12658,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12658,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12658,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12658,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12658,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12658,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12658,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12658,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12658,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12658,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12658,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12658,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12658,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12658,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12658,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12658,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12658,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12658,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12658,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12658,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12658,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12658,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12658,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12658,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12658 : FrameRepair 12658 scalarRow12658 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12658Cells j).1 (repair12658Cells j).2.1
  endpoint_upper := fun j => ((repair12658Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12658Cells j).2.2

theorem repair12659Cells (j : Fin 43) :
    0 ≤ (scalarRow12659.table (sourceIndex j)).upper ∧
    (scalarRow12659.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12659.table (sourceIndex j)).centre) /
      (scalarRow12659.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12659.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12659,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12659,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12659,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12659,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12659,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12659,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12659,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12659,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12659,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12659,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12659,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12659,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12659,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12659,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12659,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12659,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12659,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12659,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12659,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12659,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12659,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12659,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12659,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12659,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12659,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12659,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12659,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12659,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12659,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12659,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12659,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12659,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12659,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12659,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12659,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12659,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12659,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12659,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12659,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12659,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12659,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12659,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12659,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12659,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12659,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12659,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12659,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12659,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12659,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12659,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12659,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12659,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12659,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12659,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12659,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12659,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12659,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12659,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12659,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12659,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12659,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12659,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12659,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12659,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12659,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12659,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12659,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12659,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12659,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12659,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12659,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12659,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12659,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12659,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12659,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12659,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12659,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12659,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12659,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12659,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12659,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12659,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12659,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12659,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12659,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12659,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12659 : FrameRepair 12659 scalarRow12659 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12659Cells j).1 (repair12659Cells j).2.1
  endpoint_upper := fun j => ((repair12659Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12659Cells j).2.2

theorem repair12660Cells (j : Fin 43) :
    0 ≤ (scalarRow12660.table (sourceIndex j)).upper ∧
    (scalarRow12660.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12660.table (sourceIndex j)).centre) /
      (scalarRow12660.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12660.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12660,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12660,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12660,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12660,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12660,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12660,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12660,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12660,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12660,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12660,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12660,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12660,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12660,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12660,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12660,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12660,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12660,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12660,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12660,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12660,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12660,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12660,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12660,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12660,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12660,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12660,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12660,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12660,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12660,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12660,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12660,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12660,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12660,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12660,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12660,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12660,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12660,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12660,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12660,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12660,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12660,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12660,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12660,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12660,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12660,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12660,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12660,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12660,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12660,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12660,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12660,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12660,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12660,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12660,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12660,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12660,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12660,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12660,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12660,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12660,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12660,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12660,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12660,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12660,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12660,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12660,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12660,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12660,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12660,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12660,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12660,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12660,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12660,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12660,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12660,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12660,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12660,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12660,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12660,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12660,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12660,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12660,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12660,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12660,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12660,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12660,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12660 : FrameRepair 12660 scalarRow12660 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12660Cells j).1 (repair12660Cells j).2.1
  endpoint_upper := fun j => ((repair12660Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12660Cells j).2.2

theorem repair12661Cells (j : Fin 43) :
    0 ≤ (scalarRow12661.table (sourceIndex j)).upper ∧
    (scalarRow12661.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12661.table (sourceIndex j)).centre) /
      (scalarRow12661.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12661.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12661,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12661,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12661,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12661,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12661,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12661,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12661,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12661,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12661,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12661,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12661,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12661,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12661,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12661,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12661,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12661,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12661,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12661,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12661,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12661,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12661,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12661,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12661,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12661,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12661,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12661,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12661,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12661,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12661,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12661,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12661,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12661,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12661,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12661,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12661,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12661,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12661,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12661,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12661,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12661,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12661,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12661,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12661,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12661,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12661,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12661,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12661,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12661,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12661,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12661,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12661,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12661,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12661,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12661,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12661,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12661,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12661,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12661,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12661,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12661,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12661,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12661,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12661,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12661,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12661,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12661,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12661,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12661,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12661,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12661,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12661,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12661,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12661,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12661,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12661,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12661,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12661,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12661,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12661,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12661,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12661,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12661,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12661,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12661,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12661,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12661,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12661 : FrameRepair 12661 scalarRow12661 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12661Cells j).1 (repair12661Cells j).2.1
  endpoint_upper := fun j => ((repair12661Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12661Cells j).2.2

theorem repair12662Cells (j : Fin 43) :
    0 ≤ (scalarRow12662.table (sourceIndex j)).upper ∧
    (scalarRow12662.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12662.table (sourceIndex j)).centre) /
      (scalarRow12662.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12662.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12662,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12662,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12662,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12662,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12662,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12662,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12662,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12662,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12662,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12662,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12662,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12662,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12662,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12662,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12662,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12662,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12662,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12662,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12662,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12662,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12662,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12662,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12662,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12662,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12662,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12662,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12662,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12662,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12662,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12662,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12662,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12662,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12662,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12662,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12662,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12662,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12662,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12662,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12662,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12662,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12662,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12662,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12662,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12662,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12662,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12662,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12662,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12662,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12662,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12662,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12662,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12662,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12662,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12662,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12662,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12662,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12662,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12662,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12662,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12662,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12662,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12662,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12662,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12662,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12662,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12662,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12662,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12662,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12662,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12662,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12662,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12662,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12662,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12662,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12662,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12662,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12662,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12662,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12662,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12662,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12662,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12662,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12662,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12662,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12662,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12662,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12662 : FrameRepair 12662 scalarRow12662 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12662Cells j).1 (repair12662Cells j).2.1
  endpoint_upper := fun j => ((repair12662Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12662Cells j).2.2

theorem repair12663Cells (j : Fin 43) :
    0 ≤ (scalarRow12663.table (sourceIndex j)).upper ∧
    (scalarRow12663.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12663.table (sourceIndex j)).centre) /
      (scalarRow12663.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12663.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12663,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12663,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12663,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12663,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12663,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12663,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12663,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12663,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12663,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12663,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12663,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12663,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12663,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12663,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12663,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12663,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12663,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12663,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12663,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12663,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12663,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12663,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12663,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12663,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12663,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12663,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12663,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12663,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12663,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12663,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12663,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12663,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12663,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12663,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12663,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12663,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12663,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12663,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12663,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12663,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12663,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12663,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12663,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12663,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12663,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12663,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12663,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12663,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12663,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12663,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12663,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12663,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12663,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12663,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12663,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12663,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12663,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12663,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12663,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12663,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12663,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12663,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12663,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12663,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12663,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12663,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12663,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12663,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12663,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12663,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12663,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12663,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12663,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12663,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12663,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12663,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12663,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12663,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12663,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12663,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12663,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12663,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12663,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12663,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12663,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12663,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12663 : FrameRepair 12663 scalarRow12663 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12663Cells j).1 (repair12663Cells j).2.1
  endpoint_upper := fun j => ((repair12663Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12663Cells j).2.2

theorem repair12664Cells (j : Fin 43) :
    0 ≤ (scalarRow12664.table (sourceIndex j)).upper ∧
    (scalarRow12664.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12664.table (sourceIndex j)).centre) /
      (scalarRow12664.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12664.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12664,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12664,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12664,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12664,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12664,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12664,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12664,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12664,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12664,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12664,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12664,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12664,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12664,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12664,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12664,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12664,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12664,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12664,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12664,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12664,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12664,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12664,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12664,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12664,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12664,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12664,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12664,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12664,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12664,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12664,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12664,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12664,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12664,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12664,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12664,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12664,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12664,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12664,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12664,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12664,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12664,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12664,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12664,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12664,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12664,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12664,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12664,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12664,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12664,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12664,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12664,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12664,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12664,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12664,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12664,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12664,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12664,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12664,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12664,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12664,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12664,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12664,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12664,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12664,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12664,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12664,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12664,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12664,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12664,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12664,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12664,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12664,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12664,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12664,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12664,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12664,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12664,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12664,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12664,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12664,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12664,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12664,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12664,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12664,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12664,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12664,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12664 : FrameRepair 12664 scalarRow12664 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12664Cells j).1 (repair12664Cells j).2.1
  endpoint_upper := fun j => ((repair12664Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12664Cells j).2.2

theorem repair12665Cells (j : Fin 43) :
    0 ≤ (scalarRow12665.table (sourceIndex j)).upper ∧
    (scalarRow12665.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12665.table (sourceIndex j)).centre) /
      (scalarRow12665.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12665.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12665,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12665,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12665,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12665,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12665,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12665,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12665,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12665,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12665,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12665,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12665,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12665,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12665,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12665,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12665,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12665,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12665,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12665,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12665,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12665,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12665,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12665,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12665,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12665,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12665,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12665,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12665,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12665,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12665,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12665,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12665,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12665,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12665,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12665,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12665,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12665,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12665,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12665,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12665,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12665,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12665,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12665,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12665,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12665,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12665,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12665,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12665,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12665,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12665,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12665,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12665,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12665,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12665,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12665,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12665,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12665,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12665,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12665,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12665,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12665,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12665,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12665,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12665,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12665,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12665,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12665,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12665,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12665,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12665,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12665,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12665,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12665,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12665,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12665,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12665,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12665,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12665,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12665,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12665,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12665,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12665,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12665,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12665,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12665,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12665,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12665,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12665 : FrameRepair 12665 scalarRow12665 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12665Cells j).1 (repair12665Cells j).2.1
  endpoint_upper := fun j => ((repair12665Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12665Cells j).2.2

theorem repair12666Cells (j : Fin 43) :
    0 ≤ (scalarRow12666.table (sourceIndex j)).upper ∧
    (scalarRow12666.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12666.table (sourceIndex j)).centre) /
      (scalarRow12666.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12666.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12666,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12666,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12666,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12666,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12666,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12666,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12666,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12666,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12666,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12666,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12666,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12666,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12666,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12666,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12666,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12666,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12666,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12666,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12666,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12666,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12666,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12666,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12666,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12666,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12666,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12666,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12666,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12666,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12666,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12666,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12666,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12666,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12666,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12666,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12666,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12666,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12666,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12666,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12666,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12666,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12666,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12666,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12666,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12666,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12666,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12666,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12666,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12666,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12666,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12666,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12666,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12666,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12666,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12666,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12666,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12666,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12666,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12666,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12666,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12666,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12666,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12666,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12666,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12666,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12666,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12666,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12666,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12666,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12666,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12666,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12666,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12666,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12666,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12666,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12666,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12666,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12666,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12666,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12666,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12666,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12666,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12666,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12666,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12666,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12666,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12666,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12666 : FrameRepair 12666 scalarRow12666 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12666Cells j).1 (repair12666Cells j).2.1
  endpoint_upper := fun j => ((repair12666Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12666Cells j).2.2

theorem repair12667Cells (j : Fin 43) :
    0 ≤ (scalarRow12667.table (sourceIndex j)).upper ∧
    (scalarRow12667.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12667.table (sourceIndex j)).centre) /
      (scalarRow12667.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12667.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12667,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12667,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12667,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12667,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12667,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12667,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12667,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12667,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12667,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12667,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12667,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12667,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12667,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12667,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12667,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12667,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12667,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12667,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12667,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12667,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12667,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12667,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12667,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12667,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12667,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12667,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12667,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12667,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12667,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12667,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12667,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12667,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12667,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12667,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12667,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12667,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12667,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12667,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12667,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12667,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12667,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12667,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12667,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12667,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12667,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12667,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12667,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12667,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12667,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12667,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12667,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12667,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12667,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12667,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12667,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12667,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12667,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12667,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12667,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12667,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12667,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12667,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12667,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12667,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12667,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12667,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12667,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12667,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12667,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12667,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12667,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12667,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12667,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12667,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12667,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12667,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12667,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12667,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12667,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12667,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12667,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12667,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12667,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12667,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12667,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12667,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12667 : FrameRepair 12667 scalarRow12667 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12667Cells j).1 (repair12667Cells j).2.1
  endpoint_upper := fun j => ((repair12667Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12667Cells j).2.2

theorem repair12668Cells (j : Fin 43) :
    0 ≤ (scalarRow12668.table (sourceIndex j)).upper ∧
    (scalarRow12668.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12668.table (sourceIndex j)).centre) /
      (scalarRow12668.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12668.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12668,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12668,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12668,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12668,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12668,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12668,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12668,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12668,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12668,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12668,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12668,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12668,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12668,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12668,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12668,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12668,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12668,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12668,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12668,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12668,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12668,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12668,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12668,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12668,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12668,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12668,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12668,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12668,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12668,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12668,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12668,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12668,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12668,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12668,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12668,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12668,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12668,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12668,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12668,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12668,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12668,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12668,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12668,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12668,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12668,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12668,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12668,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12668,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12668,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12668,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12668,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12668,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12668,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12668,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12668,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12668,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12668,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12668,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12668,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12668,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12668,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12668,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12668,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12668,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12668,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12668,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12668,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12668,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12668,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12668,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12668,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12668,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12668,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12668,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12668,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12668,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12668,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12668,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12668,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12668,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12668,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12668,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12668,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12668,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12668,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12668,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12668 : FrameRepair 12668 scalarRow12668 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12668Cells j).1 (repair12668Cells j).2.1
  endpoint_upper := fun j => ((repair12668Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12668Cells j).2.2

theorem repair12669Cells (j : Fin 43) :
    0 ≤ (scalarRow12669.table (sourceIndex j)).upper ∧
    (scalarRow12669.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12669.table (sourceIndex j)).centre) /
      (scalarRow12669.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12669.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12669,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12669,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12669,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12669,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12669,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12669,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12669,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12669,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12669,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12669,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12669,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12669,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12669,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12669,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12669,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12669,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12669,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12669,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12669,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12669,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12669,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12669,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12669,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12669,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12669,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12669,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12669,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12669,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12669,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12669,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12669,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12669,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12669,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12669,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12669,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12669,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12669,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12669,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12669,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12669,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12669,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12669,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12669,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12669,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12669,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12669,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12669,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12669,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12669,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12669,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12669,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12669,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12669,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12669,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12669,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12669,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12669,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12669,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12669,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12669,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12669,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12669,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12669,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12669,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12669,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12669,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12669,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12669,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12669,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12669,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12669,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12669,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12669,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12669,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12669,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12669,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12669,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12669,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12669,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12669,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12669,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12669,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12669,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12669,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12669,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12669,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12669 : FrameRepair 12669 scalarRow12669 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12669Cells j).1 (repair12669Cells j).2.1
  endpoint_upper := fun j => ((repair12669Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12669Cells j).2.2

theorem repair12670Cells (j : Fin 43) :
    0 ≤ (scalarRow12670.table (sourceIndex j)).upper ∧
    (scalarRow12670.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12670.table (sourceIndex j)).centre) /
      (scalarRow12670.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12670.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12670,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12670,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12670,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12670,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12670,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12670,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12670,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12670,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12670,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12670,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12670,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12670,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12670,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12670,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12670,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12670,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12670,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12670,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12670,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12670,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12670,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12670,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12670,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12670,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12670,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12670,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12670,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12670,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12670,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12670,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12670,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12670,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12670,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12670,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12670,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12670,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12670,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12670,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12670,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12670,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12670,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12670,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12670,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12670,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12670,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12670,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12670,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12670,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12670,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12670,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12670,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12670,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12670,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12670,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12670,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12670,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12670,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12670,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12670,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12670,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12670,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12670,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12670,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12670,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12670,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12670,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12670,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12670,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12670,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12670,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12670,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12670,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12670,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12670,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12670,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12670,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12670,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12670,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12670,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12670,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12670,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12670,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12670,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12670,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12670,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12670,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12670 : FrameRepair 12670 scalarRow12670 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12670Cells j).1 (repair12670Cells j).2.1
  endpoint_upper := fun j => ((repair12670Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12670Cells j).2.2

theorem repair12671Cells (j : Fin 43) :
    0 ≤ (scalarRow12671.table (sourceIndex j)).upper ∧
    (scalarRow12671.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12671.table (sourceIndex j)).centre) /
      (scalarRow12671.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12671.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12671,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12671,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12671,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12671,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12671,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12671,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12671,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12671,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12671,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12671,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12671,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12671,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12671,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12671,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12671,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12671,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12671,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12671,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12671,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12671,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12671,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12671,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12671,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12671,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12671,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12671,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12671,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12671,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12671,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12671,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12671,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12671,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12671,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12671,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12671,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12671,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12671,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12671,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12671,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12671,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12671,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12671,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12671,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12671,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12671,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12671,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12671,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12671,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12671,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12671,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12671,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12671,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12671,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12671,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12671,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12671,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12671,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12671,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12671,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12671,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12671,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12671,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12671,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12671,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12671,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12671,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12671,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12671,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12671,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12671,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12671,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12671,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12671,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12671,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12671,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12671,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12671,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12671,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12671,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12671,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12671,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12671,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12671,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12671,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12671,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12671,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12671 : FrameRepair 12671 scalarRow12671 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12671Cells j).1 (repair12671Cells j).2.1
  endpoint_upper := fun j => ((repair12671Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12671Cells j).2.2

theorem repair12672Cells (j : Fin 43) :
    0 ≤ (scalarRow12672.table (sourceIndex j)).upper ∧
    (scalarRow12672.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12672.table (sourceIndex j)).centre) /
      (scalarRow12672.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12672.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12672,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12672,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12672,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12672,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12672,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12672,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12672,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12672,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12672,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12672,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12672,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12672,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12672,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12672,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12672,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12672,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12672,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12672,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12672,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12672,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12672,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12672,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12672,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12672,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12672,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12672,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12672,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12672,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12672,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12672,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12672,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12672,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12672,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12672,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12672,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12672,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12672,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12672,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12672,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12672,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12672,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12672,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12672,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12672,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12672,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12672,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12672,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12672,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12672,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12672,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12672,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12672,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12672,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12672,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12672,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12672,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12672,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12672,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12672,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12672,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12672,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12672,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12672,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12672,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12672,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12672,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12672,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12672,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12672,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12672,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12672,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12672,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12672,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12672,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12672,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12672,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12672,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12672,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12672,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12672,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12672,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12672,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12672,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12672,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12672,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12672,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12672 : FrameRepair 12672 scalarRow12672 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12672Cells j).1 (repair12672Cells j).2.1
  endpoint_upper := fun j => ((repair12672Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12672Cells j).2.2

theorem repair12673Cells (j : Fin 43) :
    0 ≤ (scalarRow12673.table (sourceIndex j)).upper ∧
    (scalarRow12673.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12673.table (sourceIndex j)).centre) /
      (scalarRow12673.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12673.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12673,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12673,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12673,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12673,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12673,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12673,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12673,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12673,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12673,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12673,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12673,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12673,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12673,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12673,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12673,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12673,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12673,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12673,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12673,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12673,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12673,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12673,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12673,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12673,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12673,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12673,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12673,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12673,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12673,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12673,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12673,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12673,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12673,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12673,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12673,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12673,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12673,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12673,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12673,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12673,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12673,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12673,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12673,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12673,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12673,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12673,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12673,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12673,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12673,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12673,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12673,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12673,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12673,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12673,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12673,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12673,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12673,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12673,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12673,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12673,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12673,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12673,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12673,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12673,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12673,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12673,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12673,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12673,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12673,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12673,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12673,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12673,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12673,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12673,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12673,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12673,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12673,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12673,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12673,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12673,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12673,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12673,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12673,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12673,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12673,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12673,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12673 : FrameRepair 12673 scalarRow12673 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12673Cells j).1 (repair12673Cells j).2.1
  endpoint_upper := fun j => ((repair12673Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12673Cells j).2.2

theorem repair12674Cells (j : Fin 43) :
    0 ≤ (scalarRow12674.table (sourceIndex j)).upper ∧
    (scalarRow12674.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12674.table (sourceIndex j)).centre) /
      (scalarRow12674.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12674.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12674,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12674,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12674,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12674,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12674,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12674,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12674,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12674,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12674,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12674,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12674,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12674,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12674,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12674,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12674,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12674,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12674,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12674,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12674,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12674,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12674,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12674,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12674,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12674,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12674,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12674,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12674,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12674,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12674,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12674,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12674,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12674,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12674,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12674,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12674,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12674,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12674,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12674,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12674,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12674,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12674,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12674,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12674,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12674,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12674,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12674,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12674,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12674,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12674,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12674,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12674,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12674,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12674,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12674,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12674,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12674,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12674,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12674,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12674,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12674,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12674,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12674,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12674,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12674,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12674,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12674,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12674,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12674,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12674,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12674,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12674,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12674,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12674,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12674,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12674,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12674,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12674,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12674,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12674,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12674,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12674,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12674,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12674,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12674,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12674,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12674,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12674 : FrameRepair 12674 scalarRow12674 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12674Cells j).1 (repair12674Cells j).2.1
  endpoint_upper := fun j => ((repair12674Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12674Cells j).2.2

end BstLean.Part269
