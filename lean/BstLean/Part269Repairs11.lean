import BstLean.Part269Rows11
import BstLean.Part269RepairCommon
namespace BstLean.Part269
open Real Set BstLean.Part255 BstLean.Part263 BstLean.Part264
theorem repair12625Cells (j : Fin 43) :
    0 ≤ (scalarRow12625.table (sourceIndex j)).upper ∧
    (scalarRow12625.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12625.table (sourceIndex j)).centre) /
      (scalarRow12625.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12625.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12625,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12625,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12625,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12625,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12625,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12625,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12625,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12625,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12625,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12625,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12625,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12625,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12625,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12625,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12625,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12625,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12625,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12625,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12625,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12625,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12625,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12625,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12625,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12625,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12625,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12625,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12625,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12625,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12625,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12625,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12625,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12625,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12625,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12625,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12625,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12625,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12625,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12625,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12625,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12625,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12625,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12625,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12625,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12625,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12625,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12625,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12625,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12625,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12625,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12625,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12625,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12625,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12625,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12625,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12625,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12625,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12625,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12625,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12625,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12625,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12625,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12625,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12625,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12625,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12625,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12625,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12625,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12625,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12625,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12625,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12625,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12625,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12625,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12625,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12625,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12625,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12625,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12625,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12625,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12625,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12625,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12625,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12625,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12625,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12625,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12625,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12625 : FrameRepair 12625 scalarRow12625 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12625Cells j).1 (repair12625Cells j).2.1
  endpoint_upper := fun j => ((repair12625Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12625Cells j).2.2

theorem repair12626Cells (j : Fin 43) :
    0 ≤ (scalarRow12626.table (sourceIndex j)).upper ∧
    (scalarRow12626.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12626.table (sourceIndex j)).centre) /
      (scalarRow12626.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12626.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12626,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12626,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12626,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12626,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12626,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12626,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12626,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12626,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12626,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12626,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12626,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12626,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12626,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12626,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12626,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12626,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12626,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12626,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12626,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12626,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12626,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12626,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12626,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12626,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12626,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12626,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12626,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12626,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12626,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12626,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12626,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12626,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12626,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12626,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12626,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12626,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12626,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12626,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12626,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12626,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12626,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12626,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12626,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12626,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12626,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12626,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12626,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12626,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12626,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12626,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12626,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12626,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12626,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12626,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12626,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12626,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12626,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12626,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12626,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12626,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12626,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12626,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12626,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12626,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12626,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12626,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12626,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12626,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12626,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12626,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12626,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12626,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12626,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12626,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12626,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12626,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12626,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12626,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12626,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12626,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12626,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12626,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12626,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12626,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12626,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12626,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12626 : FrameRepair 12626 scalarRow12626 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12626Cells j).1 (repair12626Cells j).2.1
  endpoint_upper := fun j => ((repair12626Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12626Cells j).2.2

theorem repair12627Cells (j : Fin 43) :
    0 ≤ (scalarRow12627.table (sourceIndex j)).upper ∧
    (scalarRow12627.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12627.table (sourceIndex j)).centre) /
      (scalarRow12627.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12627.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12627,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12627,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12627,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12627,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12627,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12627,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12627,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12627,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12627,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12627,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12627,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12627,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12627,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12627,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12627,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12627,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12627,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12627,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12627,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12627,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12627,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12627,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12627,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12627,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12627,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12627,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12627,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12627,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12627,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12627,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12627,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12627,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12627,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12627,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12627,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12627,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12627,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12627,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12627,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12627,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12627,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12627,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12627,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12627,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12627,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12627,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12627,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12627,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12627,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12627,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12627,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12627,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12627,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12627,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12627,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12627,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12627,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12627,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12627,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12627,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12627,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12627,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12627,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12627,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12627,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12627,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12627,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12627,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12627,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12627,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12627,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12627,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12627,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12627,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12627,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12627,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12627,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12627,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12627,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12627,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12627,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12627,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12627,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12627,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12627,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12627,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12627 : FrameRepair 12627 scalarRow12627 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12627Cells j).1 (repair12627Cells j).2.1
  endpoint_upper := fun j => ((repair12627Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12627Cells j).2.2

theorem repair12628Cells (j : Fin 43) :
    0 ≤ (scalarRow12628.table (sourceIndex j)).upper ∧
    (scalarRow12628.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12628.table (sourceIndex j)).centre) /
      (scalarRow12628.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12628.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12628,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12628,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12628,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12628,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12628,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12628,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12628,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12628,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12628,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12628,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12628,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12628,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12628,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12628,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12628,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12628,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12628,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12628,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12628,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12628,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12628,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12628,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12628,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12628,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12628,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12628,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12628,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12628,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12628,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12628,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12628,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12628,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12628,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12628,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12628,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12628,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12628,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12628,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12628,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12628,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12628,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12628,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12628,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12628,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12628,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12628,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12628,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12628,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12628,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12628,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12628,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12628,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12628,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12628,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12628,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12628,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12628,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12628,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12628,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12628,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12628,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12628,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12628,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12628,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12628,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12628,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12628,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12628,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12628,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12628,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12628,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12628,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12628,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12628,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12628,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12628,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12628,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12628,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12628,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12628,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12628,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12628,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12628,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12628,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12628,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12628,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12628 : FrameRepair 12628 scalarRow12628 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12628Cells j).1 (repair12628Cells j).2.1
  endpoint_upper := fun j => ((repair12628Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12628Cells j).2.2

theorem repair12629Cells (j : Fin 43) :
    0 ≤ (scalarRow12629.table (sourceIndex j)).upper ∧
    (scalarRow12629.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12629.table (sourceIndex j)).centre) /
      (scalarRow12629.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12629.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12629,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12629,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12629,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12629,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12629,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12629,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12629,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12629,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12629,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12629,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12629,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12629,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12629,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12629,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12629,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12629,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12629,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12629,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12629,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12629,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12629,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12629,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12629,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12629,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12629,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12629,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12629,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12629,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12629,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12629,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12629,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12629,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12629,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12629,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12629,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12629,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12629,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12629,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12629,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12629,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12629,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12629,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12629,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12629,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12629,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12629,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12629,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12629,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12629,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12629,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12629,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12629,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12629,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12629,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12629,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12629,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12629,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12629,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12629,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12629,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12629,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12629,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12629,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12629,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12629,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12629,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12629,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12629,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12629,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12629,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12629,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12629,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12629,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12629,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12629,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12629,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12629,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12629,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12629,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12629,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12629,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12629,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12629,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12629,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12629,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12629,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12629 : FrameRepair 12629 scalarRow12629 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12629Cells j).1 (repair12629Cells j).2.1
  endpoint_upper := fun j => ((repair12629Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12629Cells j).2.2

theorem repair12630Cells (j : Fin 43) :
    0 ≤ (scalarRow12630.table (sourceIndex j)).upper ∧
    (scalarRow12630.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12630.table (sourceIndex j)).centre) /
      (scalarRow12630.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12630.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12630,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12630,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12630,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12630,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12630,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12630,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12630,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12630,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12630,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12630,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12630,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12630,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12630,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12630,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12630,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12630,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12630,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12630,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12630,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12630,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12630,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12630,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12630,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12630,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12630,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12630,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12630,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12630,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12630,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12630,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12630,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12630,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12630,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12630,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12630,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12630,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12630,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12630,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12630,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12630,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12630,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12630,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12630,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12630,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12630,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12630,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12630,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12630,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12630,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12630,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12630,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12630,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12630,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12630,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12630,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12630,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12630,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12630,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12630,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12630,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12630,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12630,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12630,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12630,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12630,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12630,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12630,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12630,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12630,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12630,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12630,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12630,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12630,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12630,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12630,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12630,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12630,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12630,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12630,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12630,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12630,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12630,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12630,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12630,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12630,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12630,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12630 : FrameRepair 12630 scalarRow12630 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12630Cells j).1 (repair12630Cells j).2.1
  endpoint_upper := fun j => ((repair12630Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12630Cells j).2.2

theorem repair12631Cells (j : Fin 43) :
    0 ≤ (scalarRow12631.table (sourceIndex j)).upper ∧
    (scalarRow12631.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12631.table (sourceIndex j)).centre) /
      (scalarRow12631.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12631.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12631,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12631,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12631,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12631,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12631,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12631,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12631,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12631,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12631,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12631,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12631,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12631,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12631,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12631,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12631,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12631,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12631,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12631,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12631,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12631,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12631,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12631,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12631,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12631,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12631,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12631,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12631,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12631,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12631,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12631,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12631,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12631,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12631,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12631,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12631,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12631,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12631,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12631,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12631,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12631,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12631,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12631,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12631,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12631,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12631,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12631,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12631,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12631,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12631,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12631,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12631,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12631,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12631,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12631,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12631,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12631,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12631,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12631,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12631,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12631,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12631,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12631,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12631,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12631,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12631,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12631,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12631,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12631,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12631,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12631,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12631,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12631,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12631,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12631,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12631,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12631,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12631,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12631,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12631,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12631,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12631,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12631,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12631,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12631,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12631,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12631,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12631 : FrameRepair 12631 scalarRow12631 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12631Cells j).1 (repair12631Cells j).2.1
  endpoint_upper := fun j => ((repair12631Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12631Cells j).2.2

theorem repair12632Cells (j : Fin 43) :
    0 ≤ (scalarRow12632.table (sourceIndex j)).upper ∧
    (scalarRow12632.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12632.table (sourceIndex j)).centre) /
      (scalarRow12632.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12632.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12632,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12632,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12632,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12632,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12632,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12632,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12632,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12632,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12632,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12632,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12632,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12632,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12632,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12632,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12632,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12632,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12632,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12632,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12632,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12632,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12632,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12632,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12632,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12632,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12632,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12632,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12632,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12632,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12632,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12632,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12632,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12632,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12632,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12632,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12632,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12632,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12632,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12632,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12632,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12632,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12632,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12632,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12632,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12632,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12632,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12632,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12632,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12632,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12632,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12632,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12632,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12632,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12632,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12632,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12632,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12632,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12632,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12632,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12632,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12632,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12632,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12632,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12632,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12632,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12632,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12632,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12632,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12632,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12632,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12632,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12632,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12632,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12632,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12632,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12632,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12632,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12632,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12632,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12632,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12632,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12632,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12632,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12632,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12632,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12632,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12632,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12632 : FrameRepair 12632 scalarRow12632 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12632Cells j).1 (repair12632Cells j).2.1
  endpoint_upper := fun j => ((repair12632Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12632Cells j).2.2

theorem repair12633Cells (j : Fin 43) :
    0 ≤ (scalarRow12633.table (sourceIndex j)).upper ∧
    (scalarRow12633.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12633.table (sourceIndex j)).centre) /
      (scalarRow12633.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12633.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12633,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12633,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12633,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12633,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12633,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12633,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12633,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12633,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12633,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12633,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12633,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12633,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12633,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12633,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12633,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12633,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12633,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12633,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12633,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12633,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12633,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12633,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12633,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12633,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12633,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12633,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12633,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12633,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12633,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12633,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12633,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12633,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12633,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12633,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12633,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12633,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12633,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12633,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12633,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12633,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12633,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12633,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12633,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12633,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12633,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12633,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12633,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12633,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12633,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12633,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12633,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12633,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12633,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12633,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12633,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12633,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12633,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12633,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12633,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12633,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12633,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12633,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12633,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12633,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12633,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12633,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12633,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12633,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12633,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12633,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12633,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12633,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12633,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12633,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12633,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12633,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12633,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12633,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12633,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12633,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12633,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12633,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12633,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12633,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12633,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12633,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12633 : FrameRepair 12633 scalarRow12633 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12633Cells j).1 (repair12633Cells j).2.1
  endpoint_upper := fun j => ((repair12633Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12633Cells j).2.2

theorem repair12634Cells (j : Fin 43) :
    0 ≤ (scalarRow12634.table (sourceIndex j)).upper ∧
    (scalarRow12634.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12634.table (sourceIndex j)).centre) /
      (scalarRow12634.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12634.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12634,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12634,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12634,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12634,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12634,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12634,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12634,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12634,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12634,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12634,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12634,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12634,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12634,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12634,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12634,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12634,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12634,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12634,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12634,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12634,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12634,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12634,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12634,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12634,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12634,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12634,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12634,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12634,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12634,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12634,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12634,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12634,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12634,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12634,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12634,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12634,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12634,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12634,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12634,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12634,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12634,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12634,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12634,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12634,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12634,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12634,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12634,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12634,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12634,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12634,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12634,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12634,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12634,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12634,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12634,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12634,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12634,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12634,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12634,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12634,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12634,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12634,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12634,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12634,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12634,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12634,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12634,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12634,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12634,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12634,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12634,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12634,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12634,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12634,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12634,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12634,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12634,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12634,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12634,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12634,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12634,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12634,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12634,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12634,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12634,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12634,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12634 : FrameRepair 12634 scalarRow12634 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12634Cells j).1 (repair12634Cells j).2.1
  endpoint_upper := fun j => ((repair12634Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12634Cells j).2.2

theorem repair12635Cells (j : Fin 43) :
    0 ≤ (scalarRow12635.table (sourceIndex j)).upper ∧
    (scalarRow12635.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12635.table (sourceIndex j)).centre) /
      (scalarRow12635.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12635.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12635,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12635,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12635,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12635,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12635,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12635,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12635,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12635,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12635,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12635,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12635,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12635,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12635,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12635,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12635,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12635,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12635,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12635,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12635,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12635,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12635,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12635,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12635,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12635,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12635,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12635,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12635,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12635,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12635,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12635,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12635,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12635,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12635,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12635,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12635,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12635,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12635,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12635,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12635,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12635,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12635,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12635,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12635,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12635,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12635,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12635,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12635,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12635,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12635,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12635,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12635,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12635,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12635,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12635,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12635,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12635,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12635,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12635,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12635,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12635,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12635,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12635,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12635,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12635,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12635,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12635,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12635,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12635,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12635,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12635,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12635,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12635,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12635,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12635,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12635,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12635,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12635,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12635,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12635,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12635,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12635,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12635,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12635,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12635,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12635,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12635,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12635 : FrameRepair 12635 scalarRow12635 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12635Cells j).1 (repair12635Cells j).2.1
  endpoint_upper := fun j => ((repair12635Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12635Cells j).2.2

theorem repair12636Cells (j : Fin 43) :
    0 ≤ (scalarRow12636.table (sourceIndex j)).upper ∧
    (scalarRow12636.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12636.table (sourceIndex j)).centre) /
      (scalarRow12636.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12636.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12636,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12636,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12636,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12636,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12636,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12636,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12636,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12636,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12636,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12636,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12636,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12636,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12636,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12636,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12636,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12636,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12636,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12636,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12636,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12636,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12636,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12636,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12636,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12636,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12636,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12636,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12636,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12636,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12636,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12636,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12636,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12636,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12636,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12636,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12636,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12636,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12636,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12636,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12636,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12636,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12636,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12636,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12636,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12636,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12636,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12636,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12636,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12636,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12636,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12636,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12636,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12636,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12636,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12636,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12636,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12636,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12636,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12636,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12636,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12636,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12636,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12636,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12636,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12636,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12636,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12636,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12636,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12636,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12636,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12636,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12636,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12636,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12636,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12636,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12636,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12636,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12636,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12636,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12636,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12636,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12636,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12636,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12636,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12636,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12636,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12636,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12636 : FrameRepair 12636 scalarRow12636 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12636Cells j).1 (repair12636Cells j).2.1
  endpoint_upper := fun j => ((repair12636Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12636Cells j).2.2

theorem repair12637Cells (j : Fin 43) :
    0 ≤ (scalarRow12637.table (sourceIndex j)).upper ∧
    (scalarRow12637.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12637.table (sourceIndex j)).centre) /
      (scalarRow12637.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12637.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12637,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12637,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12637,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12637,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12637,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12637,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12637,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12637,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12637,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12637,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12637,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12637,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12637,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12637,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12637,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12637,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12637,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12637,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12637,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12637,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12637,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12637,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12637,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12637,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12637,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12637,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12637,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12637,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12637,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12637,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12637,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12637,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12637,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12637,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12637,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12637,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12637,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12637,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12637,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12637,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12637,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12637,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12637,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12637,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12637,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12637,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12637,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12637,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12637,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12637,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12637,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12637,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12637,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12637,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12637,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12637,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12637,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12637,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12637,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12637,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12637,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12637,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12637,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12637,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12637,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12637,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12637,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12637,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12637,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12637,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12637,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12637,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12637,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12637,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12637,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12637,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12637,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12637,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12637,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12637,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12637,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12637,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12637,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12637,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12637,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12637,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12637 : FrameRepair 12637 scalarRow12637 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12637Cells j).1 (repair12637Cells j).2.1
  endpoint_upper := fun j => ((repair12637Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12637Cells j).2.2

theorem repair12638Cells (j : Fin 43) :
    0 ≤ (scalarRow12638.table (sourceIndex j)).upper ∧
    (scalarRow12638.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12638.table (sourceIndex j)).centre) /
      (scalarRow12638.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12638.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12638,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12638,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12638,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12638,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12638,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12638,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12638,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12638,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12638,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12638,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12638,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12638,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12638,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12638,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12638,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12638,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12638,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12638,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12638,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12638,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12638,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12638,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12638,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12638,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12638,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12638,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12638,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12638,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12638,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12638,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12638,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12638,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12638,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12638,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12638,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12638,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12638,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12638,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12638,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12638,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12638,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12638,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12638,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12638,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12638,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12638,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12638,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12638,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12638,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12638,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12638,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12638,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12638,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12638,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12638,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12638,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12638,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12638,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12638,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12638,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12638,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12638,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12638,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12638,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12638,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12638,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12638,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12638,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12638,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12638,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12638,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12638,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12638,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12638,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12638,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12638,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12638,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12638,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12638,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12638,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12638,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12638,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12638,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12638,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12638,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12638,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12638 : FrameRepair 12638 scalarRow12638 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12638Cells j).1 (repair12638Cells j).2.1
  endpoint_upper := fun j => ((repair12638Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12638Cells j).2.2

theorem repair12639Cells (j : Fin 43) :
    0 ≤ (scalarRow12639.table (sourceIndex j)).upper ∧
    (scalarRow12639.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12639.table (sourceIndex j)).centre) /
      (scalarRow12639.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12639.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12639,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12639,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12639,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12639,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12639,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12639,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12639,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12639,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12639,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12639,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12639,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12639,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12639,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12639,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12639,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12639,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12639,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12639,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12639,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12639,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12639,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12639,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12639,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12639,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12639,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12639,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12639,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12639,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12639,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12639,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12639,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12639,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12639,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12639,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12639,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12639,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12639,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12639,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12639,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12639,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12639,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12639,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12639,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12639,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12639,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12639,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12639,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12639,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12639,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12639,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12639,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12639,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12639,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12639,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12639,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12639,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12639,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12639,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12639,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12639,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12639,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12639,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12639,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12639,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12639,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12639,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12639,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12639,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12639,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12639,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12639,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12639,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12639,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12639,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12639,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12639,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12639,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12639,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12639,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12639,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12639,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12639,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12639,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12639,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12639,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12639,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12639 : FrameRepair 12639 scalarRow12639 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12639Cells j).1 (repair12639Cells j).2.1
  endpoint_upper := fun j => ((repair12639Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12639Cells j).2.2

theorem repair12640Cells (j : Fin 43) :
    0 ≤ (scalarRow12640.table (sourceIndex j)).upper ∧
    (scalarRow12640.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12640.table (sourceIndex j)).centre) /
      (scalarRow12640.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12640.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12640,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12640,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12640,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12640,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12640,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12640,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12640,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12640,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12640,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12640,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12640,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12640,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12640,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12640,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12640,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12640,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12640,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12640,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12640,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12640,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12640,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12640,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12640,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12640,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12640,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12640,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12640,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12640,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12640,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12640,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12640,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12640,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12640,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12640,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12640,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12640,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12640,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12640,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12640,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12640,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12640,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12640,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12640,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12640,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12640,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12640,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12640,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12640,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12640,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12640,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12640,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12640,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12640,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12640,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12640,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12640,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12640,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12640,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12640,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12640,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12640,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12640,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12640,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12640,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12640,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12640,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12640,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12640,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12640,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12640,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12640,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12640,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12640,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12640,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12640,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12640,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12640,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12640,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12640,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12640,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12640,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12640,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12640,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12640,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12640,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12640,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12640 : FrameRepair 12640 scalarRow12640 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12640Cells j).1 (repair12640Cells j).2.1
  endpoint_upper := fun j => ((repair12640Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12640Cells j).2.2

theorem repair12641Cells (j : Fin 43) :
    0 ≤ (scalarRow12641.table (sourceIndex j)).upper ∧
    (scalarRow12641.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12641.table (sourceIndex j)).centre) /
      (scalarRow12641.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12641.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12641,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12641,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12641,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12641,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12641,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12641,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12641,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12641,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12641,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12641,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12641,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12641,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12641,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12641,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12641,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12641,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12641,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12641,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12641,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12641,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12641,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12641,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12641,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12641,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12641,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12641,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12641,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12641,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12641,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12641,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12641,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12641,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12641,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12641,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12641,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12641,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12641,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12641,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12641,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12641,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12641,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12641,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12641,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12641,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12641,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12641,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12641,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12641,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12641,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12641,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12641,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12641,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12641,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12641,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12641,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12641,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12641,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12641,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12641,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12641,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12641,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12641,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12641,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12641,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12641,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12641,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12641,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12641,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12641,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12641,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12641,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12641,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12641,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12641,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12641,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12641,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12641,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12641,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12641,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12641,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12641,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12641,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12641,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12641,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12641,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12641,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12641 : FrameRepair 12641 scalarRow12641 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12641Cells j).1 (repair12641Cells j).2.1
  endpoint_upper := fun j => ((repair12641Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12641Cells j).2.2

theorem repair12642Cells (j : Fin 43) :
    0 ≤ (scalarRow12642.table (sourceIndex j)).upper ∧
    (scalarRow12642.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12642.table (sourceIndex j)).centre) /
      (scalarRow12642.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12642.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12642,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12642,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12642,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12642,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12642,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12642,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12642,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12642,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12642,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12642,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12642,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12642,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12642,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12642,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12642,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12642,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12642,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12642,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12642,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12642,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12642,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12642,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12642,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12642,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12642,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12642,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12642,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12642,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12642,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12642,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12642,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12642,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12642,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12642,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12642,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12642,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12642,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12642,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12642,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12642,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12642,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12642,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12642,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12642,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12642,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12642,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12642,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12642,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12642,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12642,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12642,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12642,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12642,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12642,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12642,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12642,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12642,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12642,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12642,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12642,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12642,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12642,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12642,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12642,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12642,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12642,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12642,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12642,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12642,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12642,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12642,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12642,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12642,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12642,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12642,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12642,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12642,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12642,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12642,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12642,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12642,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12642,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12642,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12642,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12642,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12642,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12642 : FrameRepair 12642 scalarRow12642 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12642Cells j).1 (repair12642Cells j).2.1
  endpoint_upper := fun j => ((repair12642Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12642Cells j).2.2

theorem repair12643Cells (j : Fin 43) :
    0 ≤ (scalarRow12643.table (sourceIndex j)).upper ∧
    (scalarRow12643.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12643.table (sourceIndex j)).centre) /
      (scalarRow12643.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12643.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12643,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12643,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12643,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12643,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12643,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12643,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12643,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12643,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12643,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12643,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12643,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12643,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12643,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12643,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12643,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12643,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12643,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12643,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12643,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12643,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12643,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12643,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12643,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12643,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12643,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12643,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12643,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12643,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12643,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12643,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12643,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12643,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12643,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12643,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12643,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12643,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12643,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12643,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12643,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12643,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12643,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12643,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12643,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12643,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12643,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12643,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12643,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12643,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12643,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12643,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12643,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12643,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12643,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12643,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12643,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12643,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12643,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12643,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12643,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12643,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12643,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12643,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12643,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12643,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12643,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12643,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12643,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12643,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12643,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12643,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12643,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12643,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12643,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12643,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12643,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12643,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12643,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12643,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12643,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12643,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12643,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12643,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12643,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12643,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12643,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12643,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12643 : FrameRepair 12643 scalarRow12643 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12643Cells j).1 (repair12643Cells j).2.1
  endpoint_upper := fun j => ((repair12643Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12643Cells j).2.2

theorem repair12644Cells (j : Fin 43) :
    0 ≤ (scalarRow12644.table (sourceIndex j)).upper ∧
    (scalarRow12644.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12644.table (sourceIndex j)).centre) /
      (scalarRow12644.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12644.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12644,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12644,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12644,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12644,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12644,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12644,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12644,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12644,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12644,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12644,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12644,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12644,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12644,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12644,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12644,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12644,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12644,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12644,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12644,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12644,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12644,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12644,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12644,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12644,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12644,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12644,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12644,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12644,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12644,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12644,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12644,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12644,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12644,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12644,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12644,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12644,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12644,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12644,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12644,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12644,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12644,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12644,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12644,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12644,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12644,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12644,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12644,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12644,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12644,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12644,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12644,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12644,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12644,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12644,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12644,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12644,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12644,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12644,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12644,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12644,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12644,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12644,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12644,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12644,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12644,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12644,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12644,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12644,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12644,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12644,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12644,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12644,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12644,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12644,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12644,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12644,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12644,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12644,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12644,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12644,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12644,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12644,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12644,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12644,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12644,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12644,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12644 : FrameRepair 12644 scalarRow12644 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12644Cells j).1 (repair12644Cells j).2.1
  endpoint_upper := fun j => ((repair12644Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12644Cells j).2.2

theorem repair12645Cells (j : Fin 43) :
    0 ≤ (scalarRow12645.table (sourceIndex j)).upper ∧
    (scalarRow12645.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12645.table (sourceIndex j)).centre) /
      (scalarRow12645.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12645.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12645,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12645,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12645,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12645,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12645,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12645,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12645,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12645,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12645,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12645,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12645,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12645,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12645,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12645,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12645,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12645,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12645,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12645,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12645,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12645,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12645,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12645,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12645,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12645,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12645,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12645,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12645,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12645,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12645,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12645,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12645,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12645,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12645,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12645,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12645,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12645,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12645,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12645,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12645,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12645,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12645,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12645,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12645,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12645,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12645,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12645,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12645,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12645,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12645,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12645,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12645,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12645,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12645,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12645,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12645,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12645,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12645,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12645,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12645,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12645,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12645,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12645,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12645,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12645,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12645,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12645,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12645,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12645,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12645,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12645,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12645,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12645,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12645,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12645,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12645,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12645,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12645,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12645,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12645,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12645,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12645,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12645,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12645,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12645,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12645,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12645,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12645 : FrameRepair 12645 scalarRow12645 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12645Cells j).1 (repair12645Cells j).2.1
  endpoint_upper := fun j => ((repair12645Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12645Cells j).2.2

theorem repair12646Cells (j : Fin 43) :
    0 ≤ (scalarRow12646.table (sourceIndex j)).upper ∧
    (scalarRow12646.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12646.table (sourceIndex j)).centre) /
      (scalarRow12646.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12646.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12646,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12646,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12646,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12646,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12646,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12646,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12646,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12646,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12646,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12646,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12646,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12646,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12646,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12646,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12646,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12646,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12646,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12646,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12646,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12646,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12646,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12646,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12646,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12646,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12646,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12646,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12646,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12646,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12646,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12646,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12646,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12646,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12646,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12646,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12646,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12646,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12646,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12646,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12646,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12646,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12646,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12646,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12646,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12646,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12646,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12646,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12646,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12646,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12646,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12646,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12646,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12646,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12646,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12646,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12646,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12646,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12646,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12646,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12646,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12646,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12646,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12646,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12646,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12646,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12646,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12646,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12646,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12646,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12646,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12646,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12646,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12646,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12646,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12646,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12646,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12646,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12646,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12646,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12646,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12646,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12646,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12646,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12646,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12646,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12646,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12646,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12646 : FrameRepair 12646 scalarRow12646 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12646Cells j).1 (repair12646Cells j).2.1
  endpoint_upper := fun j => ((repair12646Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12646Cells j).2.2

theorem repair12647Cells (j : Fin 43) :
    0 ≤ (scalarRow12647.table (sourceIndex j)).upper ∧
    (scalarRow12647.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12647.table (sourceIndex j)).centre) /
      (scalarRow12647.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12647.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12647,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12647,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12647,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12647,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12647,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12647,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12647,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12647,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12647,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12647,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12647,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12647,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12647,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12647,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12647,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12647,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12647,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12647,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12647,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12647,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12647,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12647,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12647,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12647,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12647,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12647,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12647,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12647,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12647,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12647,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12647,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12647,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12647,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12647,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12647,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12647,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12647,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12647,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12647,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12647,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12647,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12647,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12647,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12647,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12647,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12647,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12647,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12647,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12647,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12647,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12647,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12647,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12647,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12647,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12647,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12647,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12647,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12647,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12647,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12647,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12647,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12647,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12647,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12647,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12647,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12647,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12647,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12647,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12647,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12647,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12647,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12647,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12647,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12647,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12647,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12647,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12647,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12647,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12647,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12647,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12647,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12647,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12647,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12647,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12647,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12647,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12647 : FrameRepair 12647 scalarRow12647 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12647Cells j).1 (repair12647Cells j).2.1
  endpoint_upper := fun j => ((repair12647Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12647Cells j).2.2

theorem repair12648Cells (j : Fin 43) :
    0 ≤ (scalarRow12648.table (sourceIndex j)).upper ∧
    (scalarRow12648.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12648.table (sourceIndex j)).centre) /
      (scalarRow12648.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12648.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12648,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12648,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12648,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12648,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12648,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12648,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12648,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12648,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12648,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12648,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12648,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12648,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12648,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12648,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12648,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12648,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12648,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12648,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12648,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12648,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12648,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12648,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12648,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12648,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12648,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12648,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12648,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12648,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12648,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12648,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12648,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12648,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12648,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12648,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12648,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12648,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12648,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12648,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12648,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12648,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12648,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12648,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12648,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12648,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12648,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12648,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12648,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12648,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12648,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12648,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12648,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12648,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12648,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12648,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12648,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12648,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12648,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12648,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12648,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12648,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12648,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12648,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12648,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12648,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12648,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12648,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12648,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12648,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12648,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12648,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12648,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12648,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12648,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12648,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12648,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12648,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12648,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12648,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12648,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12648,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12648,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12648,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12648,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12648,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12648,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12648,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12648 : FrameRepair 12648 scalarRow12648 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12648Cells j).1 (repair12648Cells j).2.1
  endpoint_upper := fun j => ((repair12648Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12648Cells j).2.2

theorem repair12649Cells (j : Fin 43) :
    0 ≤ (scalarRow12649.table (sourceIndex j)).upper ∧
    (scalarRow12649.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12649.table (sourceIndex j)).centre) /
      (scalarRow12649.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12649.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12649,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12649,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12649,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12649,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12649,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12649,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12649,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12649,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12649,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12649,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12649,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12649,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12649,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12649,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12649,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12649,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12649,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12649,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12649,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12649,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12649,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12649,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12649,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12649,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12649,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12649,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12649,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12649,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12649,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12649,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12649,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12649,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12649,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12649,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12649,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12649,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12649,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12649,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12649,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12649,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12649,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12649,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12649,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12649,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12649,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12649,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12649,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12649,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12649,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12649,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12649,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12649,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12649,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12649,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12649,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12649,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12649,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12649,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12649,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12649,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12649,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12649,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12649,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12649,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12649,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12649,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12649,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12649,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12649,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12649,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12649,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12649,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12649,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12649,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12649,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12649,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12649,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12649,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12649,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12649,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12649,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12649,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12649,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12649,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12649,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12649,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12649 : FrameRepair 12649 scalarRow12649 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12649Cells j).1 (repair12649Cells j).2.1
  endpoint_upper := fun j => ((repair12649Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12649Cells j).2.2

end BstLean.Part269
