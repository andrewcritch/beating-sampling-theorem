import BstLean.Part269Rows15
import BstLean.Part269RepairCommon
namespace BstLean.Part269
open Real Set BstLean.Part255 BstLean.Part263 BstLean.Part264
theorem repair12725Cells (j : Fin 43) :
    0 ≤ (scalarRow12725.table (sourceIndex j)).upper ∧
    (scalarRow12725.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12725.table (sourceIndex j)).centre) /
      (scalarRow12725.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12725.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12725,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12725,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12725,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12725,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12725,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12725,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12725,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12725,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12725,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12725,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12725,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12725,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12725,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12725,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12725,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12725,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12725,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12725,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12725,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12725,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12725,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12725,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12725,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12725,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12725,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12725,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12725,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12725,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12725,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12725,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12725,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12725,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12725,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12725,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12725,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12725,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12725,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12725,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12725,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12725,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12725,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12725,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12725,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12725,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12725,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12725,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12725,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12725,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12725,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12725,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12725,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12725,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12725,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12725,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12725,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12725,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12725,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12725,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12725,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12725,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12725,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12725,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12725,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12725,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12725,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12725,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12725,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12725,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12725,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12725,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12725,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12725,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12725,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12725,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12725,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12725,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12725,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12725,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12725,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12725,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12725,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12725,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12725,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12725,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12725,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12725,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12725 : FrameRepair 12725 scalarRow12725 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12725Cells j).1 (repair12725Cells j).2.1
  endpoint_upper := fun j => ((repair12725Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12725Cells j).2.2

theorem repair12726Cells (j : Fin 43) :
    0 ≤ (scalarRow12726.table (sourceIndex j)).upper ∧
    (scalarRow12726.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12726.table (sourceIndex j)).centre) /
      (scalarRow12726.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12726.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12726,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12726,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12726,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12726,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12726,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12726,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12726,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12726,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12726,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12726,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12726,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12726,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12726,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12726,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12726,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12726,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12726,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12726,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12726,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12726,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12726,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12726,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12726,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12726,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12726,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12726,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12726,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12726,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12726,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12726,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12726,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12726,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12726,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12726,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12726,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12726,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12726,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12726,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12726,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12726,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12726,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12726,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12726,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12726,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12726,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12726,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12726,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12726,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12726,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12726,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12726,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12726,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12726,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12726,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12726,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12726,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12726,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12726,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12726,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12726,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12726,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12726,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12726,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12726,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12726,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12726,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12726,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12726,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12726,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12726,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12726,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12726,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12726,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12726,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12726,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12726,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12726,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12726,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12726,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12726,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12726,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12726,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12726,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12726,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12726,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12726,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12726 : FrameRepair 12726 scalarRow12726 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12726Cells j).1 (repair12726Cells j).2.1
  endpoint_upper := fun j => ((repair12726Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12726Cells j).2.2

theorem repair12727Cells (j : Fin 43) :
    0 ≤ (scalarRow12727.table (sourceIndex j)).upper ∧
    (scalarRow12727.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12727.table (sourceIndex j)).centre) /
      (scalarRow12727.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12727.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12727,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12727,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12727,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12727,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12727,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12727,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12727,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12727,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12727,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12727,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12727,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12727,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12727,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12727,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12727,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12727,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12727,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12727,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12727,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12727,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12727,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12727,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12727,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12727,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12727,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12727,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12727,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12727,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12727,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12727,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12727,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12727,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12727,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12727,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12727,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12727,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12727,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12727,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12727,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12727,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12727,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12727,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12727,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12727,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12727,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12727,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12727,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12727,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12727,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12727,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12727,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12727,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12727,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12727,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12727,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12727,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12727,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12727,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12727,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12727,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12727,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12727,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12727,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12727,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12727,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12727,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12727,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12727,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12727,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12727,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12727,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12727,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12727,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12727,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12727,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12727,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12727,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12727,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12727,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12727,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12727,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12727,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12727,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12727,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12727,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12727,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12727 : FrameRepair 12727 scalarRow12727 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12727Cells j).1 (repair12727Cells j).2.1
  endpoint_upper := fun j => ((repair12727Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12727Cells j).2.2

theorem repair12728Cells (j : Fin 43) :
    0 ≤ (scalarRow12728.table (sourceIndex j)).upper ∧
    (scalarRow12728.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12728.table (sourceIndex j)).centre) /
      (scalarRow12728.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12728.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12728,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12728,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12728,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12728,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12728,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12728,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12728,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12728,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12728,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12728,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12728,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12728,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12728,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12728,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12728,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12728,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12728,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12728,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12728,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12728,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12728,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12728,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12728,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12728,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12728,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12728,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12728,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12728,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12728,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12728,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12728,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12728,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12728,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12728,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12728,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12728,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12728,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12728,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12728,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12728,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12728,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12728,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12728,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12728,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12728,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12728,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12728,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12728,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12728,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12728,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12728,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12728,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12728,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12728,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12728,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12728,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12728,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12728,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12728,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12728,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12728,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12728,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12728,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12728,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12728,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12728,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12728,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12728,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12728,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12728,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12728,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12728,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12728,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12728,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12728,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12728,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12728,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12728,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12728,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12728,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12728,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12728,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12728,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12728,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12728,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12728,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12728 : FrameRepair 12728 scalarRow12728 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12728Cells j).1 (repair12728Cells j).2.1
  endpoint_upper := fun j => ((repair12728Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12728Cells j).2.2

theorem repair12729Cells (j : Fin 43) :
    0 ≤ (scalarRow12729.table (sourceIndex j)).upper ∧
    (scalarRow12729.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12729.table (sourceIndex j)).centre) /
      (scalarRow12729.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12729.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12729,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12729,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12729,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12729,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12729,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12729,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12729,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12729,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12729,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12729,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12729,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12729,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12729,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12729,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12729,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12729,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12729,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12729,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12729,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12729,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12729,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12729,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12729,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12729,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12729,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12729,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12729,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12729,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12729,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12729,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12729,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12729,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12729,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12729,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12729,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12729,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12729,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12729,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12729,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12729,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12729,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12729,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12729,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12729,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12729,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12729,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12729,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12729,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12729,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12729,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12729,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12729,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12729,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12729,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12729,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12729,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12729,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12729,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12729,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12729,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12729,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12729,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12729,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12729,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12729,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12729,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12729,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12729,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12729,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12729,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12729,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12729,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12729,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12729,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12729,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12729,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12729,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12729,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12729,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12729,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12729,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12729,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12729,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12729,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12729,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12729,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12729 : FrameRepair 12729 scalarRow12729 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12729Cells j).1 (repair12729Cells j).2.1
  endpoint_upper := fun j => ((repair12729Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12729Cells j).2.2

theorem repair12730Cells (j : Fin 43) :
    0 ≤ (scalarRow12730.table (sourceIndex j)).upper ∧
    (scalarRow12730.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12730.table (sourceIndex j)).centre) /
      (scalarRow12730.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12730.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12730,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12730,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12730,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12730,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12730,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12730,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12730,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12730,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12730,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12730,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12730,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12730,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12730,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12730,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12730,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12730,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12730,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12730,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12730,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12730,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12730,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12730,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12730,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12730,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12730,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12730,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12730,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12730,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12730,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12730,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12730,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12730,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12730,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12730,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12730,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12730,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12730,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12730,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12730,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12730,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12730,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12730,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12730,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12730,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12730,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12730,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12730,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12730,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12730,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12730,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12730,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12730,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12730,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12730,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12730,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12730,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12730,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12730,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12730,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12730,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12730,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12730,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12730,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12730,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12730,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12730,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12730,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12730,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12730,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12730,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12730,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12730,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12730,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12730,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12730,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12730,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12730,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12730,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12730,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12730,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12730,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12730,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12730,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12730,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12730,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12730,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12730 : FrameRepair 12730 scalarRow12730 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12730Cells j).1 (repair12730Cells j).2.1
  endpoint_upper := fun j => ((repair12730Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12730Cells j).2.2

theorem repair12731Cells (j : Fin 43) :
    0 ≤ (scalarRow12731.table (sourceIndex j)).upper ∧
    (scalarRow12731.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12731.table (sourceIndex j)).centre) /
      (scalarRow12731.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12731.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12731,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12731,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12731,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12731,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12731,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12731,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12731,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12731,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12731,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12731,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12731,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12731,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12731,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12731,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12731,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12731,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12731,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12731,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12731,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12731,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12731,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12731,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12731,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12731,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12731,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12731,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12731,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12731,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12731,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12731,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12731,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12731,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12731,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12731,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12731,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12731,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12731,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12731,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12731,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12731,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12731,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12731,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12731,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12731,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12731,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12731,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12731,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12731,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12731,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12731,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12731,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12731,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12731,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12731,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12731,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12731,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12731,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12731,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12731,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12731,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12731,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12731,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12731,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12731,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12731,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12731,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12731,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12731,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12731,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12731,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12731,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12731,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12731,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12731,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12731,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12731,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12731,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12731,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12731,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12731,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12731,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12731,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12731,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12731,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12731,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12731,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12731 : FrameRepair 12731 scalarRow12731 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12731Cells j).1 (repair12731Cells j).2.1
  endpoint_upper := fun j => ((repair12731Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12731Cells j).2.2

theorem repair12732Cells (j : Fin 43) :
    0 ≤ (scalarRow12732.table (sourceIndex j)).upper ∧
    (scalarRow12732.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12732.table (sourceIndex j)).centre) /
      (scalarRow12732.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12732.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12732,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12732,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12732,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12732,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12732,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12732,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12732,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12732,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12732,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12732,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12732,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12732,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12732,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12732,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12732,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12732,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12732,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12732,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12732,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12732,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12732,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12732,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12732,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12732,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12732,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12732,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12732,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12732,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12732,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12732,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12732,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12732,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12732,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12732,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12732,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12732,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12732,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12732,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12732,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12732,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12732,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12732,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12732,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12732,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12732,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12732,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12732,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12732,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12732,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12732,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12732,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12732,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12732,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12732,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12732,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12732,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12732,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12732,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12732,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12732,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12732,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12732,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12732,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12732,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12732,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12732,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12732,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12732,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12732,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12732,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12732,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12732,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12732,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12732,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12732,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12732,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12732,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12732,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12732,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12732,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12732,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12732,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12732,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12732,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12732,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12732,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12732 : FrameRepair 12732 scalarRow12732 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12732Cells j).1 (repair12732Cells j).2.1
  endpoint_upper := fun j => ((repair12732Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12732Cells j).2.2

theorem repair12733Cells (j : Fin 43) :
    0 ≤ (scalarRow12733.table (sourceIndex j)).upper ∧
    (scalarRow12733.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12733.table (sourceIndex j)).centre) /
      (scalarRow12733.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12733.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12733,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12733,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12733,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12733,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12733,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12733,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12733,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12733,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12733,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12733,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12733,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12733,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12733,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12733,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12733,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12733,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12733,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12733,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12733,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12733,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12733,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12733,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12733,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12733,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12733,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12733,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12733,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12733,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12733,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12733,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12733,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12733,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12733,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12733,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12733,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12733,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12733,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12733,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12733,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12733,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12733,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12733,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12733,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12733,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12733,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12733,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12733,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12733,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12733,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12733,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12733,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12733,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12733,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12733,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12733,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12733,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12733,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12733,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12733,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12733,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12733,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12733,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12733,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12733,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12733,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12733,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12733,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12733,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12733,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12733,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12733,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12733,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12733,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12733,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12733,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12733,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12733,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12733,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12733,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12733,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12733,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12733,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12733,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12733,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12733,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12733,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12733 : FrameRepair 12733 scalarRow12733 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12733Cells j).1 (repair12733Cells j).2.1
  endpoint_upper := fun j => ((repair12733Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12733Cells j).2.2

theorem repair12734Cells (j : Fin 43) :
    0 ≤ (scalarRow12734.table (sourceIndex j)).upper ∧
    (scalarRow12734.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12734.table (sourceIndex j)).centre) /
      (scalarRow12734.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12734.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12734,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12734,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12734,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12734,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12734,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12734,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12734,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12734,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12734,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12734,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12734,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12734,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12734,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12734,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12734,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12734,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12734,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12734,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12734,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12734,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12734,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12734,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12734,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12734,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12734,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12734,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12734,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12734,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12734,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12734,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12734,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12734,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12734,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12734,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12734,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12734,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12734,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12734,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12734,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12734,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12734,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12734,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12734,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12734,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12734,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12734,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12734,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12734,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12734,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12734,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12734,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12734,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12734,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12734,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12734,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12734,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12734,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12734,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12734,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12734,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12734,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12734,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12734,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12734,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12734,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12734,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12734,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12734,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12734,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12734,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12734,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12734,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12734,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12734,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12734,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12734,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12734,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12734,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12734,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12734,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12734,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12734,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12734,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12734,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12734,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12734,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12734 : FrameRepair 12734 scalarRow12734 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12734Cells j).1 (repair12734Cells j).2.1
  endpoint_upper := fun j => ((repair12734Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12734Cells j).2.2

theorem repair12735Cells (j : Fin 43) :
    0 ≤ (scalarRow12735.table (sourceIndex j)).upper ∧
    (scalarRow12735.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12735.table (sourceIndex j)).centre) /
      (scalarRow12735.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12735.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12735,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12735,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12735,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12735,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12735,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12735,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12735,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12735,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12735,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12735,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12735,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12735,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12735,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12735,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12735,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12735,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12735,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12735,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12735,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12735,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12735,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12735,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12735,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12735,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12735,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12735,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12735,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12735,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12735,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12735,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12735,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12735,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12735,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12735,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12735,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12735,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12735,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12735,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12735,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12735,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12735,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12735,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12735,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12735,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12735,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12735,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12735,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12735,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12735,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12735,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12735,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12735,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12735,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12735,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12735,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12735,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12735,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12735,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12735,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12735,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12735,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12735,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12735,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12735,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12735,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12735,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12735,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12735,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12735,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12735,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12735,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12735,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12735,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12735,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12735,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12735,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12735,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12735,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12735,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12735,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12735,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12735,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12735,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12735,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12735,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12735,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12735 : FrameRepair 12735 scalarRow12735 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12735Cells j).1 (repair12735Cells j).2.1
  endpoint_upper := fun j => ((repair12735Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12735Cells j).2.2

theorem repair12736Cells (j : Fin 43) :
    0 ≤ (scalarRow12736.table (sourceIndex j)).upper ∧
    (scalarRow12736.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12736.table (sourceIndex j)).centre) /
      (scalarRow12736.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12736.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12736,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12736,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12736,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12736,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12736,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12736,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12736,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12736,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12736,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12736,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12736,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12736,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12736,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12736,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12736,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12736,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12736,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12736,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12736,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12736,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12736,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12736,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12736,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12736,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12736,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12736,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12736,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12736,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12736,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12736,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12736,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12736,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12736,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12736,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12736,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12736,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12736,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12736,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12736,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12736,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12736,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12736,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12736,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12736,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12736,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12736,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12736,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12736,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12736,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12736,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12736,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12736,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12736,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12736,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12736,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12736,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12736,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12736,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12736,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12736,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12736,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12736,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12736,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12736,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12736,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12736,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12736,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12736,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12736,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12736,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12736,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12736,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12736,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12736,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12736,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12736,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12736,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12736,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12736,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12736,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12736,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12736,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12736,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12736,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12736,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12736,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12736 : FrameRepair 12736 scalarRow12736 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12736Cells j).1 (repair12736Cells j).2.1
  endpoint_upper := fun j => ((repair12736Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12736Cells j).2.2

theorem repair12737Cells (j : Fin 43) :
    0 ≤ (scalarRow12737.table (sourceIndex j)).upper ∧
    (scalarRow12737.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12737.table (sourceIndex j)).centre) /
      (scalarRow12737.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12737.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12737,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12737,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12737,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12737,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12737,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12737,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12737,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12737,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12737,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12737,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12737,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12737,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12737,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12737,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12737,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12737,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12737,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12737,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12737,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12737,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12737,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12737,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12737,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12737,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12737,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12737,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12737,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12737,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12737,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12737,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12737,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12737,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12737,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12737,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12737,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12737,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12737,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12737,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12737,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12737,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12737,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12737,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12737,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12737,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12737,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12737,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12737,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12737,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12737,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12737,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12737,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12737,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12737,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12737,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12737,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12737,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12737,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12737,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12737,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12737,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12737,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12737,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12737,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12737,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12737,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12737,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12737,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12737,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12737,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12737,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12737,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12737,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12737,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12737,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12737,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12737,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12737,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12737,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12737,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12737,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12737,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12737,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12737,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12737,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12737,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12737,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12737 : FrameRepair 12737 scalarRow12737 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12737Cells j).1 (repair12737Cells j).2.1
  endpoint_upper := fun j => ((repair12737Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12737Cells j).2.2

theorem repair12738Cells (j : Fin 43) :
    0 ≤ (scalarRow12738.table (sourceIndex j)).upper ∧
    (scalarRow12738.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12738.table (sourceIndex j)).centre) /
      (scalarRow12738.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12738.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12738,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12738,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12738,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12738,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12738,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12738,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12738,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12738,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12738,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12738,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12738,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12738,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12738,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12738,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12738,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12738,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12738,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12738,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12738,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12738,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12738,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12738,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12738,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12738,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12738,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12738,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12738,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12738,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12738,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12738,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12738,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12738,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12738,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12738,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12738,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12738,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12738,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12738,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12738,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12738,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12738,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12738,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12738,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12738,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12738,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12738,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12738,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12738,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12738,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12738,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12738,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12738,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12738,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12738,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12738,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12738,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12738,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12738,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12738,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12738,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12738,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12738,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12738,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12738,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12738,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12738,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12738,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12738,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12738,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12738,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12738,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12738,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12738,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12738,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12738,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12738,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12738,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12738,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12738,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12738,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12738,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12738,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12738,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12738,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12738,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12738,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12738 : FrameRepair 12738 scalarRow12738 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12738Cells j).1 (repair12738Cells j).2.1
  endpoint_upper := fun j => ((repair12738Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12738Cells j).2.2

theorem repair12739Cells (j : Fin 43) :
    0 ≤ (scalarRow12739.table (sourceIndex j)).upper ∧
    (scalarRow12739.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12739.table (sourceIndex j)).centre) /
      (scalarRow12739.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12739.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12739,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12739,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12739,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12739,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12739,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12739,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12739,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12739,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12739,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12739,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12739,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12739,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12739,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12739,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12739,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12739,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12739,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12739,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12739,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12739,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12739,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12739,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12739,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12739,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12739,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12739,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12739,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12739,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12739,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12739,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12739,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12739,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12739,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12739,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12739,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12739,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12739,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12739,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12739,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12739,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12739,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12739,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12739,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12739,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12739,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12739,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12739,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12739,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12739,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12739,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12739,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12739,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12739,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12739,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12739,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12739,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12739,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12739,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12739,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12739,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12739,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12739,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12739,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12739,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12739,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12739,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12739,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12739,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12739,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12739,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12739,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12739,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12739,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12739,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12739,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12739,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12739,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12739,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12739,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12739,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12739,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12739,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12739,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12739,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12739,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12739,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12739 : FrameRepair 12739 scalarRow12739 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12739Cells j).1 (repair12739Cells j).2.1
  endpoint_upper := fun j => ((repair12739Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12739Cells j).2.2

theorem repair12740Cells (j : Fin 43) :
    0 ≤ (scalarRow12740.table (sourceIndex j)).upper ∧
    (scalarRow12740.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12740.table (sourceIndex j)).centre) /
      (scalarRow12740.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12740.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12740,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12740,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12740,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12740,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12740,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12740,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12740,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12740,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12740,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12740,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12740,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12740,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12740,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12740,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12740,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12740,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12740,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12740,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12740,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12740,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12740,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12740,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12740,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12740,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12740,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12740,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12740,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12740,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12740,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12740,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12740,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12740,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12740,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12740,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12740,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12740,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12740,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12740,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12740,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12740,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12740,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12740,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12740,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12740,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12740,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12740,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12740,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12740,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12740,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12740,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12740,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12740,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12740,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12740,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12740,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12740,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12740,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12740,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12740,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12740,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12740,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12740,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12740,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12740,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12740,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12740,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12740,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12740,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12740,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12740,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12740,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12740,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12740,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12740,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12740,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12740,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12740,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12740,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12740,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12740,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12740,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12740,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12740,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12740,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12740,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12740,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12740 : FrameRepair 12740 scalarRow12740 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12740Cells j).1 (repair12740Cells j).2.1
  endpoint_upper := fun j => ((repair12740Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12740Cells j).2.2

theorem repair12741Cells (j : Fin 43) :
    0 ≤ (scalarRow12741.table (sourceIndex j)).upper ∧
    (scalarRow12741.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12741.table (sourceIndex j)).centre) /
      (scalarRow12741.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12741.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12741,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12741,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12741,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12741,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12741,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12741,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12741,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12741,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12741,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12741,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12741,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12741,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12741,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12741,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12741,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12741,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12741,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12741,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12741,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12741,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12741,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12741,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12741,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12741,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12741,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12741,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12741,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12741,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12741,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12741,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12741,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12741,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12741,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12741,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12741,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12741,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12741,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12741,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12741,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12741,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12741,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12741,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12741,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12741,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12741,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12741,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12741,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12741,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12741,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12741,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12741,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12741,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12741,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12741,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12741,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12741,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12741,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12741,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12741,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12741,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12741,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12741,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12741,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12741,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12741,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12741,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12741,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12741,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12741,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12741,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12741,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12741,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12741,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12741,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12741,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12741,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12741,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12741,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12741,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12741,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12741,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12741,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12741,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12741,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12741,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12741,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12741 : FrameRepair 12741 scalarRow12741 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12741Cells j).1 (repair12741Cells j).2.1
  endpoint_upper := fun j => ((repair12741Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12741Cells j).2.2

theorem repair12742Cells (j : Fin 43) :
    0 ≤ (scalarRow12742.table (sourceIndex j)).upper ∧
    (scalarRow12742.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12742.table (sourceIndex j)).centre) /
      (scalarRow12742.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12742.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12742,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12742,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12742,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12742,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12742,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12742,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12742,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12742,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12742,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12742,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12742,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12742,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12742,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12742,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12742,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12742,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12742,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12742,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12742,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12742,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12742,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12742,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12742,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12742,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12742,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12742,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12742,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12742,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12742,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12742,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12742,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12742,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12742,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12742,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12742,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12742,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12742,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12742,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12742,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12742,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12742,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12742,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12742,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12742,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12742,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12742,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12742,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12742,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12742,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12742,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12742,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12742,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12742,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12742,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12742,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12742,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12742,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12742,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12742,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12742,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12742,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12742,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12742,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12742,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12742,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12742,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12742,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12742,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12742,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12742,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12742,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12742,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12742,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12742,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12742,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12742,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12742,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12742,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12742,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12742,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12742,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12742,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12742,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12742,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12742,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12742,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12742 : FrameRepair 12742 scalarRow12742 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12742Cells j).1 (repair12742Cells j).2.1
  endpoint_upper := fun j => ((repair12742Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12742Cells j).2.2

theorem repair12743Cells (j : Fin 43) :
    0 ≤ (scalarRow12743.table (sourceIndex j)).upper ∧
    (scalarRow12743.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12743.table (sourceIndex j)).centre) /
      (scalarRow12743.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12743.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12743,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12743,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12743,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12743,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12743,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12743,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12743,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12743,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12743,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12743,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12743,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12743,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12743,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12743,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12743,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12743,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12743,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12743,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12743,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12743,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12743,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12743,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12743,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12743,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12743,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12743,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12743,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12743,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12743,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12743,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12743,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12743,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12743,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12743,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12743,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12743,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12743,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12743,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12743,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12743,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12743,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12743,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12743,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12743,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12743,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12743,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12743,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12743,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12743,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12743,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12743,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12743,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12743,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12743,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12743,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12743,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12743,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12743,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12743,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12743,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12743,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12743,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12743,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12743,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12743,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12743,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12743,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12743,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12743,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12743,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12743,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12743,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12743,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12743,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12743,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12743,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12743,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12743,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12743,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12743,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12743,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12743,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12743,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12743,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12743,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12743,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12743 : FrameRepair 12743 scalarRow12743 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12743Cells j).1 (repair12743Cells j).2.1
  endpoint_upper := fun j => ((repair12743Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12743Cells j).2.2

theorem repair12744Cells (j : Fin 43) :
    0 ≤ (scalarRow12744.table (sourceIndex j)).upper ∧
    (scalarRow12744.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12744.table (sourceIndex j)).centre) /
      (scalarRow12744.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12744.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12744,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12744,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12744,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12744,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12744,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12744,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12744,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12744,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12744,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12744,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12744,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12744,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12744,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12744,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12744,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12744,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12744,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12744,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12744,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12744,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12744,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12744,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12744,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12744,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12744,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12744,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12744,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12744,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12744,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12744,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12744,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12744,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12744,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12744,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12744,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12744,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12744,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12744,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12744,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12744,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12744,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12744,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12744,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12744,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12744,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12744,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12744,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12744,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12744,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12744,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12744,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12744,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12744,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12744,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12744,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12744,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12744,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12744,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12744,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12744,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12744,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12744,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12744,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12744,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12744,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12744,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12744,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12744,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12744,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12744,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12744,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12744,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12744,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12744,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12744,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12744,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12744,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12744,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12744,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12744,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12744,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12744,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12744,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12744,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12744,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12744,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12744 : FrameRepair 12744 scalarRow12744 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12744Cells j).1 (repair12744Cells j).2.1
  endpoint_upper := fun j => ((repair12744Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12744Cells j).2.2

theorem repair12745Cells (j : Fin 43) :
    0 ≤ (scalarRow12745.table (sourceIndex j)).upper ∧
    (scalarRow12745.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12745.table (sourceIndex j)).centre) /
      (scalarRow12745.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12745.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12745,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12745,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12745,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12745,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12745,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12745,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12745,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12745,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12745,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12745,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12745,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12745,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12745,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12745,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12745,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12745,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12745,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12745,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12745,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12745,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12745,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12745,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12745,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12745,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12745,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12745,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12745,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12745,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12745,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12745,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12745,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12745,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12745,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12745,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12745,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12745,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12745,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12745,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12745,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12745,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12745,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12745,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12745,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12745,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12745,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12745,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12745,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12745,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12745,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12745,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12745,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12745,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12745,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12745,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12745,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12745,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12745,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12745,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12745,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12745,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12745,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12745,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12745,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12745,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12745,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12745,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12745,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12745,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12745,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12745,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12745,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12745,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12745,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12745,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12745,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12745,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12745,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12745,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12745,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12745,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12745,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12745,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12745,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12745,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12745,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12745,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12745 : FrameRepair 12745 scalarRow12745 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12745Cells j).1 (repair12745Cells j).2.1
  endpoint_upper := fun j => ((repair12745Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12745Cells j).2.2

theorem repair12746Cells (j : Fin 43) :
    0 ≤ (scalarRow12746.table (sourceIndex j)).upper ∧
    (scalarRow12746.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12746.table (sourceIndex j)).centre) /
      (scalarRow12746.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12746.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12746,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12746,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12746,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12746,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12746,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12746,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12746,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12746,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12746,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12746,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12746,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12746,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12746,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12746,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12746,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12746,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12746,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12746,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12746,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12746,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12746,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12746,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12746,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12746,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12746,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12746,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12746,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12746,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12746,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12746,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12746,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12746,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12746,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12746,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12746,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12746,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12746,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12746,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12746,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12746,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12746,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12746,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12746,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12746,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12746,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12746,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12746,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12746,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12746,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12746,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12746,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12746,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12746,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12746,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12746,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12746,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12746,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12746,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12746,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12746,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12746,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12746,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12746,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12746,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12746,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12746,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12746,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12746,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12746,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12746,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12746,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12746,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12746,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12746,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12746,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12746,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12746,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12746,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12746,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12746,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12746,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12746,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12746,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12746,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12746,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12746,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12746 : FrameRepair 12746 scalarRow12746 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12746Cells j).1 (repair12746Cells j).2.1
  endpoint_upper := fun j => ((repair12746Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12746Cells j).2.2

theorem repair12747Cells (j : Fin 43) :
    0 ≤ (scalarRow12747.table (sourceIndex j)).upper ∧
    (scalarRow12747.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12747.table (sourceIndex j)).centre) /
      (scalarRow12747.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12747.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12747,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12747,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12747,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12747,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12747,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12747,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12747,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12747,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12747,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12747,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12747,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12747,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12747,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12747,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12747,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12747,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12747,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12747,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12747,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12747,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12747,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12747,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12747,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12747,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12747,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12747,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12747,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12747,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12747,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12747,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12747,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12747,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12747,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12747,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12747,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12747,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12747,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12747,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12747,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12747,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12747,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12747,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12747,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12747,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12747,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12747,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12747,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12747,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12747,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12747,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12747,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12747,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12747,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12747,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12747,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12747,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12747,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12747,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12747,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12747,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12747,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12747,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12747,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12747,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12747,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12747,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12747,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12747,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12747,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12747,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12747,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12747,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12747,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12747,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12747,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12747,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12747,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12747,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12747,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12747,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12747,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12747,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12747,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12747,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12747,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12747,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12747 : FrameRepair 12747 scalarRow12747 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12747Cells j).1 (repair12747Cells j).2.1
  endpoint_upper := fun j => ((repair12747Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12747Cells j).2.2

theorem repair12748Cells (j : Fin 43) :
    0 ≤ (scalarRow12748.table (sourceIndex j)).upper ∧
    (scalarRow12748.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12748.table (sourceIndex j)).centre) /
      (scalarRow12748.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12748.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12748,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12748,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12748,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12748,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12748,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12748,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12748,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12748,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12748,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12748,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12748,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12748,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12748,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12748,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12748,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12748,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12748,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12748,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12748,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12748,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12748,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12748,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12748,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12748,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12748,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12748,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12748,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12748,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12748,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12748,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12748,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12748,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12748,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12748,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12748,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12748,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12748,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12748,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12748,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12748,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12748,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12748,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12748,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12748,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12748,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12748,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12748,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12748,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12748,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12748,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12748,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12748,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12748,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12748,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12748,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12748,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12748,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12748,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12748,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12748,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12748,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12748,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12748,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12748,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12748,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12748,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12748,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12748,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12748,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12748,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12748,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12748,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12748,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12748,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12748,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12748,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12748,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12748,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12748,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12748,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12748,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12748,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12748,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12748,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12748,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12748,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12748 : FrameRepair 12748 scalarRow12748 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12748Cells j).1 (repair12748Cells j).2.1
  endpoint_upper := fun j => ((repair12748Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12748Cells j).2.2

theorem repair12749Cells (j : Fin 43) :
    0 ≤ (scalarRow12749.table (sourceIndex j)).upper ∧
    (scalarRow12749.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12749.table (sourceIndex j)).centre) /
      (scalarRow12749.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12749.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12749,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12749,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12749,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12749,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12749,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12749,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12749,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12749,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12749,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12749,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12749,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12749,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12749,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12749,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12749,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12749,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12749,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12749,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12749,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12749,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12749,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12749,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12749,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12749,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12749,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12749,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12749,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12749,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12749,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12749,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12749,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12749,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12749,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12749,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12749,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12749,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12749,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12749,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12749,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12749,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12749,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12749,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12749,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12749,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12749,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12749,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12749,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12749,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12749,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12749,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12749,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12749,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12749,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12749,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12749,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12749,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12749,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12749,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12749,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12749,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12749,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12749,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12749,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12749,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12749,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12749,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12749,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12749,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12749,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12749,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12749,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12749,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12749,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12749,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12749,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12749,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12749,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12749,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12749,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12749,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12749,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12749,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12749,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12749,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12749,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12749,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12749 : FrameRepair 12749 scalarRow12749 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12749Cells j).1 (repair12749Cells j).2.1
  endpoint_upper := fun j => ((repair12749Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12749Cells j).2.2

end BstLean.Part269
