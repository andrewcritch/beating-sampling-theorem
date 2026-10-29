import BstLean.Part269Rows5
import BstLean.Part269RepairCommon
namespace BstLean.Part269
open Real Set BstLean.Part255 BstLean.Part263 BstLean.Part264
theorem repair12475Cells (j : Fin 43) :
    0 ≤ (scalarRow12475.table (sourceIndex j)).upper ∧
    (scalarRow12475.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12475.table (sourceIndex j)).centre) /
      (scalarRow12475.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12475.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12475,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12475,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12475,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12475,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12475,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12475,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12475,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12475,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12475,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12475,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12475,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12475,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12475,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12475,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12475,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12475,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12475,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12475,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12475,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12475,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12475,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12475,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12475,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12475,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12475,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12475,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12475,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12475,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12475,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12475,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12475,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12475,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12475,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12475,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12475,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12475,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12475,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12475,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12475,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12475,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12475,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12475,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12475,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12475,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12475,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12475,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12475,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12475,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12475,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12475,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12475,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12475,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12475,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12475,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12475,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12475,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12475,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12475,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12475,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12475,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12475,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12475,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12475,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12475,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12475,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12475,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12475,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12475,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12475,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12475,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12475,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12475,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12475,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12475,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12475,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12475,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12475,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12475,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12475,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12475,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12475,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12475,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12475,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12475,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12475,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12475,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12475 : FrameRepair 12475 scalarRow12475 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12475Cells j).1 (repair12475Cells j).2.1
  endpoint_upper := fun j => ((repair12475Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12475Cells j).2.2

theorem repair12476Cells (j : Fin 43) :
    0 ≤ (scalarRow12476.table (sourceIndex j)).upper ∧
    (scalarRow12476.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12476.table (sourceIndex j)).centre) /
      (scalarRow12476.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12476.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12476,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12476,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12476,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12476,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12476,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12476,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12476,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12476,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12476,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12476,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12476,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12476,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12476,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12476,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12476,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12476,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12476,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12476,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12476,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12476,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12476,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12476,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12476,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12476,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12476,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12476,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12476,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12476,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12476,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12476,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12476,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12476,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12476,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12476,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12476,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12476,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12476,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12476,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12476,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12476,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12476,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12476,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12476,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12476,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12476,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12476,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12476,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12476,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12476,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12476,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12476,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12476,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12476,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12476,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12476,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12476,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12476,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12476,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12476,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12476,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12476,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12476,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12476,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12476,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12476,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12476,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12476,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12476,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12476,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12476,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12476,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12476,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12476,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12476,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12476,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12476,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12476,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12476,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12476,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12476,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12476,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12476,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12476,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12476,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12476,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12476,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12476 : FrameRepair 12476 scalarRow12476 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12476Cells j).1 (repair12476Cells j).2.1
  endpoint_upper := fun j => ((repair12476Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12476Cells j).2.2

theorem repair12477Cells (j : Fin 43) :
    0 ≤ (scalarRow12477.table (sourceIndex j)).upper ∧
    (scalarRow12477.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12477.table (sourceIndex j)).centre) /
      (scalarRow12477.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12477.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12477,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12477,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12477,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12477,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12477,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12477,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12477,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12477,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12477,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12477,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12477,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12477,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12477,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12477,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12477,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12477,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12477,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12477,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12477,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12477,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12477,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12477,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12477,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12477,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12477,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12477,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12477,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12477,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12477,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12477,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12477,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12477,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12477,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12477,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12477,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12477,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12477,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12477,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12477,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12477,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12477,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12477,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12477,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12477,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12477,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12477,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12477,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12477,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12477,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12477,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12477,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12477,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12477,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12477,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12477,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12477,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12477,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12477,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12477,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12477,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12477,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12477,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12477,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12477,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12477,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12477,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12477,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12477,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12477,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12477,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12477,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12477,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12477,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12477,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12477,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12477,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12477,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12477,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12477,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12477,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12477,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12477,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12477,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12477,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12477,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12477,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12477 : FrameRepair 12477 scalarRow12477 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12477Cells j).1 (repair12477Cells j).2.1
  endpoint_upper := fun j => ((repair12477Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12477Cells j).2.2

theorem repair12478Cells (j : Fin 43) :
    0 ≤ (scalarRow12478.table (sourceIndex j)).upper ∧
    (scalarRow12478.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12478.table (sourceIndex j)).centre) /
      (scalarRow12478.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12478.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12478,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12478,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12478,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12478,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12478,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12478,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12478,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12478,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12478,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12478,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12478,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12478,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12478,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12478,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12478,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12478,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12478,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12478,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12478,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12478,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12478,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12478,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12478,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12478,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12478,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12478,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12478,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12478,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12478,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12478,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12478,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12478,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12478,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12478,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12478,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12478,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12478,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12478,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12478,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12478,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12478,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12478,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12478,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12478,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12478,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12478,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12478,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12478,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12478,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12478,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12478,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12478,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12478,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12478,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12478,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12478,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12478,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12478,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12478,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12478,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12478,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12478,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12478,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12478,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12478,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12478,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12478,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12478,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12478,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12478,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12478,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12478,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12478,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12478,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12478,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12478,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12478,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12478,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12478,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12478,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12478,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12478,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12478,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12478,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12478,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12478,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12478 : FrameRepair 12478 scalarRow12478 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12478Cells j).1 (repair12478Cells j).2.1
  endpoint_upper := fun j => ((repair12478Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12478Cells j).2.2

theorem repair12479Cells (j : Fin 43) :
    0 ≤ (scalarRow12479.table (sourceIndex j)).upper ∧
    (scalarRow12479.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12479.table (sourceIndex j)).centre) /
      (scalarRow12479.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12479.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12479,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12479,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12479,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12479,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12479,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12479,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12479,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12479,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12479,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12479,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12479,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12479,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12479,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12479,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12479,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12479,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12479,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12479,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12479,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12479,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12479,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12479,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12479,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12479,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12479,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12479,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12479,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12479,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12479,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12479,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12479,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12479,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12479,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12479,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12479,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12479,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12479,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12479,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12479,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12479,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12479,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12479,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12479,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12479,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12479,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12479,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12479,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12479,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12479,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12479,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12479,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12479,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12479,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12479,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12479,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12479,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12479,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12479,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12479,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12479,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12479,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12479,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12479,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12479,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12479,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12479,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12479,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12479,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12479,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12479,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12479,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12479,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12479,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12479,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12479,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12479,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12479,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12479,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12479,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12479,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12479,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12479,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12479,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12479,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12479,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12479,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12479 : FrameRepair 12479 scalarRow12479 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12479Cells j).1 (repair12479Cells j).2.1
  endpoint_upper := fun j => ((repair12479Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12479Cells j).2.2

theorem repair12480Cells (j : Fin 43) :
    0 ≤ (scalarRow12480.table (sourceIndex j)).upper ∧
    (scalarRow12480.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12480.table (sourceIndex j)).centre) /
      (scalarRow12480.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12480.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12480,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12480,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12480,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12480,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12480,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12480,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12480,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12480,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12480,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12480,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12480,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12480,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12480,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12480,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12480,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12480,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12480,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12480,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12480,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12480,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12480,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12480,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12480,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12480,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12480,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12480,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12480,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12480,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12480,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12480,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12480,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12480,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12480,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12480,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12480,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12480,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12480,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12480,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12480,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12480,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12480,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12480,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12480,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12480,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12480,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12480,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12480,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12480,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12480,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12480,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12480,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12480,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12480,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12480,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12480,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12480,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12480,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12480,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12480,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12480,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12480,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12480,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12480,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12480,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12480,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12480,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12480,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12480,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12480,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12480,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12480,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12480,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12480,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12480,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12480,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12480,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12480,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12480,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12480,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12480,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12480,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12480,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12480,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12480,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12480,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12480,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12480 : FrameRepair 12480 scalarRow12480 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12480Cells j).1 (repair12480Cells j).2.1
  endpoint_upper := fun j => ((repair12480Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12480Cells j).2.2

theorem repair12481Cells (j : Fin 43) :
    0 ≤ (scalarRow12481.table (sourceIndex j)).upper ∧
    (scalarRow12481.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12481.table (sourceIndex j)).centre) /
      (scalarRow12481.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12481.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12481,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12481,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12481,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12481,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12481,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12481,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12481,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12481,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12481,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12481,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12481,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12481,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12481,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12481,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12481,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12481,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12481,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12481,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12481,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12481,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12481,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12481,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12481,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12481,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12481,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12481,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12481,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12481,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12481,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12481,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12481,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12481,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12481,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12481,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12481,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12481,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12481,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12481,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12481,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12481,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12481,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12481,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12481,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12481,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12481,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12481,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12481,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12481,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12481,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12481,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12481,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12481,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12481,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12481,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12481,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12481,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12481,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12481,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12481,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12481,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12481,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12481,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12481,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12481,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12481,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12481,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12481,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12481,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12481,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12481,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12481,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12481,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12481,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12481,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12481,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12481,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12481,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12481,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12481,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12481,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12481,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12481,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12481,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12481,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12481,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12481,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12481 : FrameRepair 12481 scalarRow12481 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12481Cells j).1 (repair12481Cells j).2.1
  endpoint_upper := fun j => ((repair12481Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12481Cells j).2.2

theorem repair12482Cells (j : Fin 43) :
    0 ≤ (scalarRow12482.table (sourceIndex j)).upper ∧
    (scalarRow12482.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12482.table (sourceIndex j)).centre) /
      (scalarRow12482.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12482.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12482,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12482,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12482,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12482,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12482,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12482,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12482,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12482,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12482,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12482,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12482,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12482,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12482,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12482,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12482,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12482,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12482,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12482,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12482,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12482,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12482,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12482,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12482,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12482,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12482,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12482,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12482,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12482,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12482,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12482,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12482,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12482,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12482,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12482,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12482,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12482,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12482,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12482,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12482,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12482,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12482,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12482,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12482,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12482,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12482,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12482,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12482,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12482,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12482,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12482,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12482,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12482,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12482,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12482,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12482,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12482,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12482,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12482,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12482,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12482,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12482,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12482,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12482,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12482,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12482,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12482,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12482,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12482,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12482,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12482,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12482,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12482,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12482,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12482,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12482,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12482,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12482,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12482,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12482,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12482,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12482,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12482,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12482,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12482,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12482,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12482,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12482 : FrameRepair 12482 scalarRow12482 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12482Cells j).1 (repair12482Cells j).2.1
  endpoint_upper := fun j => ((repair12482Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12482Cells j).2.2

theorem repair12483Cells (j : Fin 43) :
    0 ≤ (scalarRow12483.table (sourceIndex j)).upper ∧
    (scalarRow12483.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12483.table (sourceIndex j)).centre) /
      (scalarRow12483.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12483.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12483,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12483,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12483,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12483,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12483,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12483,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12483,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12483,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12483,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12483,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12483,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12483,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12483,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12483,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12483,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12483,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12483,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12483,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12483,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12483,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12483,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12483,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12483,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12483,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12483,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12483,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12483,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12483,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12483,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12483,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12483,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12483,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12483,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12483,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12483,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12483,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12483,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12483,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12483,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12483,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12483,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12483,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12483,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12483,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12483,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12483,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12483,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12483,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12483,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12483,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12483,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12483,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12483,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12483,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12483,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12483,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12483,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12483,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12483,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12483,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12483,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12483,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12483,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12483,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12483,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12483,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12483,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12483,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12483,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12483,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12483,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12483,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12483,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12483,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12483,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12483,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12483,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12483,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12483,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12483,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12483,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12483,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12483,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12483,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12483,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12483,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12483 : FrameRepair 12483 scalarRow12483 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12483Cells j).1 (repair12483Cells j).2.1
  endpoint_upper := fun j => ((repair12483Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12483Cells j).2.2

theorem repair12484Cells (j : Fin 43) :
    0 ≤ (scalarRow12484.table (sourceIndex j)).upper ∧
    (scalarRow12484.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12484.table (sourceIndex j)).centre) /
      (scalarRow12484.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12484.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12484,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12484,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12484,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12484,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12484,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12484,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12484,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12484,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12484,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12484,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12484,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12484,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12484,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12484,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12484,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12484,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12484,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12484,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12484,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12484,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12484,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12484,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12484,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12484,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12484,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12484,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12484,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12484,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12484,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12484,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12484,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12484,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12484,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12484,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12484,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12484,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12484,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12484,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12484,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12484,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12484,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12484,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12484,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12484,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12484,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12484,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12484,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12484,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12484,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12484,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12484,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12484,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12484,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12484,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12484,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12484,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12484,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12484,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12484,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12484,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12484,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12484,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12484,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12484,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12484,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12484,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12484,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12484,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12484,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12484,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12484,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12484,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12484,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12484,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12484,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12484,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12484,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12484,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12484,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12484,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12484,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12484,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12484,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12484,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12484,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12484,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12484 : FrameRepair 12484 scalarRow12484 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12484Cells j).1 (repair12484Cells j).2.1
  endpoint_upper := fun j => ((repair12484Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12484Cells j).2.2

theorem repair12485Cells (j : Fin 43) :
    0 ≤ (scalarRow12485.table (sourceIndex j)).upper ∧
    (scalarRow12485.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12485.table (sourceIndex j)).centre) /
      (scalarRow12485.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12485.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12485,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12485,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12485,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12485,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12485,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12485,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12485,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12485,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12485,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12485,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12485,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12485,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12485,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12485,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12485,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12485,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12485,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12485,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12485,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12485,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12485,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12485,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12485,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12485,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12485,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12485,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12485,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12485,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12485,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12485,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12485,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12485,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12485,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12485,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12485,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12485,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12485,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12485,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12485,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12485,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12485,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12485,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12485,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12485,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12485,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12485,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12485,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12485,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12485,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12485,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12485,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12485,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12485,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12485,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12485,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12485,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12485,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12485,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12485,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12485,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12485,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12485,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12485,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12485,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12485,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12485,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12485,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12485,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12485,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12485,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12485,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12485,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12485,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12485,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12485,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12485,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12485,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12485,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12485,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12485,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12485,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12485,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12485,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12485,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12485,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12485,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12485 : FrameRepair 12485 scalarRow12485 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12485Cells j).1 (repair12485Cells j).2.1
  endpoint_upper := fun j => ((repair12485Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12485Cells j).2.2

theorem repair12486Cells (j : Fin 43) :
    0 ≤ (scalarRow12486.table (sourceIndex j)).upper ∧
    (scalarRow12486.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12486.table (sourceIndex j)).centre) /
      (scalarRow12486.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12486.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12486,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12486,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12486,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12486,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12486,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12486,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12486,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12486,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12486,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12486,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12486,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12486,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12486,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12486,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12486,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12486,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12486,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12486,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12486,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12486,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12486,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12486,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12486,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12486,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12486,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12486,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12486,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12486,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12486,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12486,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12486,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12486,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12486,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12486,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12486,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12486,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12486,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12486,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12486,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12486,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12486,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12486,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12486,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12486,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12486,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12486,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12486,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12486,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12486,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12486,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12486,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12486,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12486,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12486,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12486,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12486,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12486,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12486,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12486,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12486,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12486,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12486,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12486,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12486,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12486,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12486,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12486,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12486,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12486,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12486,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12486,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12486,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12486,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12486,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12486,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12486,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12486,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12486,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12486,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12486,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12486,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12486,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12486,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12486,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12486,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12486,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12486 : FrameRepair 12486 scalarRow12486 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12486Cells j).1 (repair12486Cells j).2.1
  endpoint_upper := fun j => ((repair12486Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12486Cells j).2.2

theorem repair12487Cells (j : Fin 43) :
    0 ≤ (scalarRow12487.table (sourceIndex j)).upper ∧
    (scalarRow12487.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12487.table (sourceIndex j)).centre) /
      (scalarRow12487.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12487.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12487,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12487,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12487,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12487,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12487,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12487,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12487,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12487,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12487,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12487,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12487,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12487,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12487,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12487,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12487,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12487,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12487,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12487,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12487,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12487,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12487,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12487,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12487,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12487,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12487,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12487,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12487,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12487,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12487,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12487,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12487,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12487,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12487,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12487,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12487,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12487,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12487,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12487,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12487,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12487,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12487,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12487,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12487,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12487,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12487,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12487,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12487,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12487,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12487,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12487,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12487,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12487,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12487,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12487,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12487,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12487,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12487,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12487,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12487,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12487,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12487,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12487,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12487,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12487,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12487,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12487,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12487,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12487,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12487,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12487,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12487,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12487,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12487,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12487,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12487,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12487,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12487,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12487,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12487,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12487,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12487,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12487,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12487,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12487,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12487,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12487,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12487 : FrameRepair 12487 scalarRow12487 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12487Cells j).1 (repair12487Cells j).2.1
  endpoint_upper := fun j => ((repair12487Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12487Cells j).2.2

theorem repair12488Cells (j : Fin 43) :
    0 ≤ (scalarRow12488.table (sourceIndex j)).upper ∧
    (scalarRow12488.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12488.table (sourceIndex j)).centre) /
      (scalarRow12488.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12488.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12488,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12488,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12488,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12488,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12488,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12488,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12488,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12488,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12488,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12488,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12488,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12488,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12488,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12488,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12488,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12488,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12488,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12488,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12488,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12488,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12488,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12488,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12488,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12488,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12488,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12488,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12488,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12488,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12488,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12488,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12488,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12488,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12488,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12488,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12488,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12488,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12488,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12488,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12488,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12488,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12488,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12488,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12488,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12488,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12488,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12488,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12488,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12488,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12488,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12488,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12488,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12488,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12488,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12488,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12488,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12488,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12488,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12488,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12488,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12488,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12488,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12488,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12488,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12488,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12488,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12488,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12488,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12488,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12488,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12488,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12488,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12488,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12488,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12488,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12488,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12488,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12488,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12488,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12488,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12488,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12488,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12488,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12488,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12488,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12488,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12488,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12488 : FrameRepair 12488 scalarRow12488 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12488Cells j).1 (repair12488Cells j).2.1
  endpoint_upper := fun j => ((repair12488Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12488Cells j).2.2

theorem repair12489Cells (j : Fin 43) :
    0 ≤ (scalarRow12489.table (sourceIndex j)).upper ∧
    (scalarRow12489.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12489.table (sourceIndex j)).centre) /
      (scalarRow12489.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12489.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12489,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12489,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12489,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12489,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12489,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12489,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12489,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12489,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12489,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12489,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12489,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12489,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12489,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12489,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12489,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12489,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12489,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12489,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12489,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12489,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12489,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12489,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12489,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12489,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12489,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12489,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12489,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12489,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12489,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12489,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12489,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12489,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12489,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12489,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12489,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12489,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12489,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12489,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12489,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12489,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12489,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12489,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12489,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12489,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12489,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12489,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12489,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12489,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12489,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12489,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12489,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12489,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12489,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12489,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12489,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12489,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12489,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12489,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12489,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12489,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12489,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12489,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12489,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12489,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12489,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12489,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12489,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12489,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12489,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12489,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12489,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12489,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12489,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12489,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12489,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12489,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12489,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12489,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12489,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12489,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12489,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12489,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12489,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12489,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12489,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12489,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12489 : FrameRepair 12489 scalarRow12489 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12489Cells j).1 (repair12489Cells j).2.1
  endpoint_upper := fun j => ((repair12489Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12489Cells j).2.2

theorem repair12490Cells (j : Fin 43) :
    0 ≤ (scalarRow12490.table (sourceIndex j)).upper ∧
    (scalarRow12490.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12490.table (sourceIndex j)).centre) /
      (scalarRow12490.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12490.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12490,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12490,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12490,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12490,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12490,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12490,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12490,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12490,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12490,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12490,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12490,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12490,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12490,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12490,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12490,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12490,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12490,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12490,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12490,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12490,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12490,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12490,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12490,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12490,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12490,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12490,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12490,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12490,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12490,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12490,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12490,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12490,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12490,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12490,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12490,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12490,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12490,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12490,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12490,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12490,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12490,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12490,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12490,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12490,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12490,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12490,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12490,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12490,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12490,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12490,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12490,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12490,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12490,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12490,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12490,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12490,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12490,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12490,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12490,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12490,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12490,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12490,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12490,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12490,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12490,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12490,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12490,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12490,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12490,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12490,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12490,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12490,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12490,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12490,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12490,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12490,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12490,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12490,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12490,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12490,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12490,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12490,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12490,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12490,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12490,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12490,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12490 : FrameRepair 12490 scalarRow12490 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12490Cells j).1 (repair12490Cells j).2.1
  endpoint_upper := fun j => ((repair12490Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12490Cells j).2.2

theorem repair12491Cells (j : Fin 43) :
    0 ≤ (scalarRow12491.table (sourceIndex j)).upper ∧
    (scalarRow12491.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12491.table (sourceIndex j)).centre) /
      (scalarRow12491.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12491.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12491,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12491,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12491,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12491,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12491,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12491,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12491,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12491,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12491,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12491,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12491,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12491,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12491,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12491,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12491,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12491,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12491,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12491,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12491,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12491,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12491,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12491,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12491,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12491,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12491,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12491,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12491,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12491,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12491,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12491,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12491,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12491,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12491,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12491,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12491,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12491,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12491,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12491,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12491,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12491,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12491,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12491,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12491,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12491,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12491,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12491,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12491,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12491,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12491,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12491,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12491,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12491,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12491,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12491,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12491,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12491,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12491,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12491,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12491,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12491,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12491,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12491,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12491,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12491,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12491,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12491,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12491,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12491,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12491,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12491,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12491,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12491,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12491,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12491,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12491,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12491,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12491,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12491,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12491,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12491,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12491,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12491,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12491,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12491,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12491,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12491,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12491 : FrameRepair 12491 scalarRow12491 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12491Cells j).1 (repair12491Cells j).2.1
  endpoint_upper := fun j => ((repair12491Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12491Cells j).2.2

theorem repair12492Cells (j : Fin 43) :
    0 ≤ (scalarRow12492.table (sourceIndex j)).upper ∧
    (scalarRow12492.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12492.table (sourceIndex j)).centre) /
      (scalarRow12492.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12492.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12492,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12492,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12492,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12492,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12492,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12492,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12492,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12492,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12492,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12492,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12492,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12492,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12492,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12492,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12492,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12492,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12492,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12492,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12492,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12492,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12492,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12492,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12492,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12492,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12492,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12492,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12492,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12492,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12492,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12492,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12492,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12492,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12492,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12492,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12492,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12492,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12492,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12492,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12492,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12492,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12492,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12492,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12492,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12492,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12492,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12492,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12492,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12492,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12492,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12492,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12492,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12492,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12492,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12492,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12492,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12492,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12492,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12492,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12492,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12492,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12492,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12492,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12492,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12492,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12492,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12492,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12492,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12492,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12492,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12492,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12492,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12492,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12492,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12492,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12492,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12492,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12492,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12492,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12492,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12492,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12492,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12492,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12492,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12492,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12492,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12492,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12492 : FrameRepair 12492 scalarRow12492 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12492Cells j).1 (repair12492Cells j).2.1
  endpoint_upper := fun j => ((repair12492Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12492Cells j).2.2

theorem repair12493Cells (j : Fin 43) :
    0 ≤ (scalarRow12493.table (sourceIndex j)).upper ∧
    (scalarRow12493.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12493.table (sourceIndex j)).centre) /
      (scalarRow12493.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12493.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12493,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12493,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12493,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12493,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12493,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12493,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12493,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12493,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12493,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12493,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12493,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12493,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12493,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12493,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12493,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12493,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12493,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12493,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12493,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12493,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12493,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12493,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12493,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12493,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12493,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12493,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12493,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12493,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12493,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12493,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12493,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12493,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12493,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12493,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12493,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12493,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12493,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12493,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12493,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12493,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12493,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12493,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12493,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12493,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12493,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12493,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12493,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12493,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12493,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12493,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12493,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12493,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12493,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12493,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12493,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12493,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12493,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12493,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12493,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12493,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12493,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12493,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12493,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12493,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12493,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12493,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12493,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12493,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12493,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12493,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12493,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12493,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12493,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12493,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12493,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12493,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12493,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12493,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12493,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12493,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12493,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12493,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12493,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12493,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12493,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12493,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12493 : FrameRepair 12493 scalarRow12493 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12493Cells j).1 (repair12493Cells j).2.1
  endpoint_upper := fun j => ((repair12493Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12493Cells j).2.2

theorem repair12494Cells (j : Fin 43) :
    0 ≤ (scalarRow12494.table (sourceIndex j)).upper ∧
    (scalarRow12494.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12494.table (sourceIndex j)).centre) /
      (scalarRow12494.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12494.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12494,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12494,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12494,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12494,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12494,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12494,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12494,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12494,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12494,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12494,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12494,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12494,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12494,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12494,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12494,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12494,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12494,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12494,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12494,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12494,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12494,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12494,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12494,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12494,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12494,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12494,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12494,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12494,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12494,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12494,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12494,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12494,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12494,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12494,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12494,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12494,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12494,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12494,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12494,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12494,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12494,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12494,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12494,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12494,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12494,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12494,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12494,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12494,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12494,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12494,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12494,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12494,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12494,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12494,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12494,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12494,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12494,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12494,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12494,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12494,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12494,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12494,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12494,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12494,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12494,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12494,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12494,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12494,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12494,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12494,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12494,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12494,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12494,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12494,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12494,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12494,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12494,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12494,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12494,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12494,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12494,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12494,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12494,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12494,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12494,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12494,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12494 : FrameRepair 12494 scalarRow12494 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12494Cells j).1 (repair12494Cells j).2.1
  endpoint_upper := fun j => ((repair12494Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12494Cells j).2.2

theorem repair12495Cells (j : Fin 43) :
    0 ≤ (scalarRow12495.table (sourceIndex j)).upper ∧
    (scalarRow12495.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12495.table (sourceIndex j)).centre) /
      (scalarRow12495.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12495.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12495,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12495,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12495,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12495,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12495,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12495,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12495,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12495,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12495,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12495,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12495,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12495,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12495,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12495,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12495,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12495,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12495,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12495,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12495,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12495,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12495,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12495,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12495,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12495,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12495,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12495,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12495,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12495,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12495,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12495,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12495,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12495,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12495,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12495,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12495,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12495,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12495,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12495,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12495,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12495,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12495,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12495,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12495,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12495,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12495,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12495,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12495,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12495,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12495,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12495,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12495,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12495,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12495,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12495,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12495,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12495,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12495,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12495,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12495,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12495,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12495,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12495,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12495,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12495,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12495,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12495,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12495,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12495,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12495,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12495,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12495,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12495,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12495,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12495,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12495,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12495,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12495,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12495,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12495,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12495,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12495,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12495,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12495,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12495,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12495,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12495,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12495 : FrameRepair 12495 scalarRow12495 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12495Cells j).1 (repair12495Cells j).2.1
  endpoint_upper := fun j => ((repair12495Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12495Cells j).2.2

theorem repair12496Cells (j : Fin 43) :
    0 ≤ (scalarRow12496.table (sourceIndex j)).upper ∧
    (scalarRow12496.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12496.table (sourceIndex j)).centre) /
      (scalarRow12496.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12496.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12496,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12496,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12496,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12496,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12496,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12496,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12496,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12496,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12496,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12496,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12496,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12496,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12496,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12496,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12496,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12496,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12496,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12496,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12496,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12496,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12496,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12496,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12496,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12496,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12496,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12496,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12496,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12496,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12496,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12496,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12496,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12496,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12496,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12496,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12496,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12496,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12496,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12496,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12496,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12496,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12496,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12496,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12496,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12496,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12496,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12496,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12496,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12496,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12496,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12496,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12496,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12496,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12496,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12496,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12496,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12496,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12496,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12496,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12496,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12496,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12496,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12496,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12496,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12496,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12496,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12496,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12496,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12496,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12496,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12496,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12496,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12496,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12496,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12496,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12496,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12496,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12496,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12496,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12496,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12496,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12496,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12496,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12496,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12496,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12496,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12496,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12496 : FrameRepair 12496 scalarRow12496 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12496Cells j).1 (repair12496Cells j).2.1
  endpoint_upper := fun j => ((repair12496Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12496Cells j).2.2

theorem repair12497Cells (j : Fin 43) :
    0 ≤ (scalarRow12497.table (sourceIndex j)).upper ∧
    (scalarRow12497.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12497.table (sourceIndex j)).centre) /
      (scalarRow12497.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12497.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12497,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12497,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12497,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12497,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12497,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12497,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12497,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12497,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12497,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12497,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12497,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12497,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12497,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12497,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12497,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12497,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12497,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12497,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12497,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12497,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12497,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12497,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12497,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12497,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12497,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12497,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12497,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12497,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12497,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12497,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12497,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12497,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12497,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12497,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12497,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12497,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12497,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12497,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12497,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12497,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12497,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12497,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12497,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12497,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12497,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12497,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12497,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12497,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12497,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12497,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12497,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12497,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12497,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12497,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12497,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12497,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12497,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12497,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12497,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12497,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12497,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12497,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12497,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12497,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12497,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12497,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12497,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12497,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12497,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12497,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12497,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12497,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12497,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12497,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12497,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12497,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12497,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12497,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12497,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12497,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12497,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12497,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12497,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12497,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12497,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12497,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12497 : FrameRepair 12497 scalarRow12497 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12497Cells j).1 (repair12497Cells j).2.1
  endpoint_upper := fun j => ((repair12497Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12497Cells j).2.2

theorem repair12498Cells (j : Fin 43) :
    0 ≤ (scalarRow12498.table (sourceIndex j)).upper ∧
    (scalarRow12498.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12498.table (sourceIndex j)).centre) /
      (scalarRow12498.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12498.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12498,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12498,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12498,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12498,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12498,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12498,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12498,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12498,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12498,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12498,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12498,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12498,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12498,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12498,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12498,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12498,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12498,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12498,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12498,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12498,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12498,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12498,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12498,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12498,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12498,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12498,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12498,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12498,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12498,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12498,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12498,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12498,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12498,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12498,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12498,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12498,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12498,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12498,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12498,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12498,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12498,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12498,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12498,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12498,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12498,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12498,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12498,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12498,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12498,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12498,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12498,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12498,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12498,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12498,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12498,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12498,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12498,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12498,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12498,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12498,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12498,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12498,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12498,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12498,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12498,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12498,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12498,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12498,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12498,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12498,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12498,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12498,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12498,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12498,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12498,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12498,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12498,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12498,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12498,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12498,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12498,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12498,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12498,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12498,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12498,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12498,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12498 : FrameRepair 12498 scalarRow12498 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12498Cells j).1 (repair12498Cells j).2.1
  endpoint_upper := fun j => ((repair12498Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12498Cells j).2.2

theorem repair12499Cells (j : Fin 43) :
    0 ≤ (scalarRow12499.table (sourceIndex j)).upper ∧
    (scalarRow12499.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12499.table (sourceIndex j)).centre) /
      (scalarRow12499.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12499.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12499,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12499,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12499,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12499,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12499,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12499,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12499,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12499,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12499,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12499,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12499,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12499,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12499,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12499,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12499,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12499,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12499,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12499,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12499,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12499,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12499,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12499,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12499,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12499,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12499,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12499,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12499,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12499,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12499,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12499,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12499,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12499,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12499,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12499,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12499,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12499,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12499,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12499,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12499,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12499,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12499,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12499,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12499,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12499,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12499,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12499,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12499,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12499,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12499,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12499,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12499,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12499,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12499,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12499,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12499,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12499,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12499,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12499,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12499,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12499,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12499,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12499,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12499,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12499,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12499,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12499,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12499,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12499,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12499,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12499,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12499,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12499,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12499,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12499,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12499,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12499,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12499,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12499,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12499,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12499,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12499,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12499,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12499,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12499,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12499,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12499,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12499 : FrameRepair 12499 scalarRow12499 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12499Cells j).1 (repair12499Cells j).2.1
  endpoint_upper := fun j => ((repair12499Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12499Cells j).2.2

end BstLean.Part269
