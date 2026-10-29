import BstLean.Part269Rows13
import BstLean.Part269RepairCommon
namespace BstLean.Part269
open Real Set BstLean.Part255 BstLean.Part263 BstLean.Part264
theorem repair12675Cells (j : Fin 43) :
    0 ≤ (scalarRow12675.table (sourceIndex j)).upper ∧
    (scalarRow12675.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12675.table (sourceIndex j)).centre) /
      (scalarRow12675.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12675.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12675,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12675,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12675,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12675,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12675,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12675,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12675,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12675,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12675,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12675,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12675,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12675,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12675,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12675,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12675,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12675,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12675,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12675,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12675,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12675,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12675,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12675,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12675,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12675,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12675,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12675,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12675,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12675,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12675,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12675,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12675,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12675,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12675,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12675,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12675,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12675,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12675,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12675,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12675,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12675,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12675,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12675,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12675,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12675,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12675,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12675,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12675,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12675,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12675,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12675,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12675,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12675,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12675,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12675,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12675,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12675,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12675,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12675,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12675,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12675,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12675,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12675,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12675,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12675,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12675,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12675,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12675,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12675,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12675,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12675,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12675,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12675,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12675,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12675,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12675,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12675,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12675,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12675,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12675,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12675,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12675,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12675,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12675,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12675,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12675,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12675,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12675 : FrameRepair 12675 scalarRow12675 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12675Cells j).1 (repair12675Cells j).2.1
  endpoint_upper := fun j => ((repair12675Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12675Cells j).2.2

theorem repair12676Cells (j : Fin 43) :
    0 ≤ (scalarRow12676.table (sourceIndex j)).upper ∧
    (scalarRow12676.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12676.table (sourceIndex j)).centre) /
      (scalarRow12676.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12676.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12676,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12676,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12676,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12676,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12676,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12676,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12676,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12676,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12676,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12676,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12676,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12676,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12676,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12676,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12676,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12676,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12676,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12676,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12676,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12676,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12676,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12676,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12676,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12676,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12676,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12676,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12676,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12676,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12676,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12676,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12676,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12676,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12676,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12676,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12676,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12676,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12676,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12676,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12676,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12676,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12676,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12676,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12676,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12676,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12676,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12676,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12676,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12676,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12676,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12676,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12676,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12676,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12676,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12676,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12676,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12676,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12676,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12676,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12676,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12676,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12676,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12676,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12676,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12676,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12676,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12676,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12676,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12676,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12676,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12676,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12676,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12676,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12676,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12676,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12676,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12676,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12676,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12676,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12676,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12676,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12676,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12676,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12676,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12676,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12676,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12676,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12676 : FrameRepair 12676 scalarRow12676 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12676Cells j).1 (repair12676Cells j).2.1
  endpoint_upper := fun j => ((repair12676Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12676Cells j).2.2

theorem repair12677Cells (j : Fin 43) :
    0 ≤ (scalarRow12677.table (sourceIndex j)).upper ∧
    (scalarRow12677.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12677.table (sourceIndex j)).centre) /
      (scalarRow12677.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12677.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12677,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12677,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12677,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12677,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12677,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12677,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12677,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12677,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12677,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12677,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12677,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12677,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12677,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12677,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12677,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12677,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12677,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12677,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12677,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12677,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12677,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12677,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12677,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12677,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12677,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12677,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12677,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12677,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12677,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12677,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12677,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12677,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12677,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12677,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12677,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12677,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12677,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12677,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12677,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12677,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12677,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12677,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12677,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12677,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12677,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12677,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12677,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12677,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12677,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12677,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12677,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12677,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12677,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12677,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12677,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12677,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12677,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12677,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12677,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12677,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12677,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12677,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12677,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12677,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12677,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12677,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12677,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12677,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12677,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12677,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12677,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12677,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12677,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12677,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12677,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12677,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12677,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12677,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12677,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12677,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12677,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12677,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12677,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12677,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12677,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12677,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12677 : FrameRepair 12677 scalarRow12677 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12677Cells j).1 (repair12677Cells j).2.1
  endpoint_upper := fun j => ((repair12677Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12677Cells j).2.2

theorem repair12678Cells (j : Fin 43) :
    0 ≤ (scalarRow12678.table (sourceIndex j)).upper ∧
    (scalarRow12678.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12678.table (sourceIndex j)).centre) /
      (scalarRow12678.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12678.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12678,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12678,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12678,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12678,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12678,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12678,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12678,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12678,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12678,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12678,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12678,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12678,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12678,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12678,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12678,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12678,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12678,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12678,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12678,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12678,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12678,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12678,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12678,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12678,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12678,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12678,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12678,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12678,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12678,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12678,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12678,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12678,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12678,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12678,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12678,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12678,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12678,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12678,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12678,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12678,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12678,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12678,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12678,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12678,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12678,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12678,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12678,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12678,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12678,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12678,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12678,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12678,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12678,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12678,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12678,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12678,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12678,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12678,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12678,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12678,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12678,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12678,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12678,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12678,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12678,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12678,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12678,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12678,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12678,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12678,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12678,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12678,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12678,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12678,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12678,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12678,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12678,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12678,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12678,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12678,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12678,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12678,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12678,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12678,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12678,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12678,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12678 : FrameRepair 12678 scalarRow12678 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12678Cells j).1 (repair12678Cells j).2.1
  endpoint_upper := fun j => ((repair12678Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12678Cells j).2.2

theorem repair12679Cells (j : Fin 43) :
    0 ≤ (scalarRow12679.table (sourceIndex j)).upper ∧
    (scalarRow12679.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12679.table (sourceIndex j)).centre) /
      (scalarRow12679.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12679.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12679,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12679,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12679,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12679,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12679,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12679,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12679,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12679,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12679,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12679,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12679,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12679,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12679,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12679,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12679,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12679,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12679,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12679,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12679,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12679,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12679,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12679,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12679,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12679,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12679,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12679,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12679,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12679,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12679,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12679,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12679,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12679,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12679,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12679,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12679,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12679,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12679,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12679,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12679,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12679,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12679,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12679,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12679,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12679,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12679,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12679,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12679,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12679,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12679,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12679,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12679,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12679,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12679,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12679,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12679,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12679,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12679,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12679,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12679,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12679,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12679,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12679,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12679,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12679,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12679,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12679,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12679,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12679,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12679,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12679,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12679,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12679,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12679,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12679,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12679,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12679,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12679,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12679,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12679,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12679,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12679,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12679,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12679,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12679,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12679,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12679,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12679 : FrameRepair 12679 scalarRow12679 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12679Cells j).1 (repair12679Cells j).2.1
  endpoint_upper := fun j => ((repair12679Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12679Cells j).2.2

theorem repair12680Cells (j : Fin 43) :
    0 ≤ (scalarRow12680.table (sourceIndex j)).upper ∧
    (scalarRow12680.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12680.table (sourceIndex j)).centre) /
      (scalarRow12680.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12680.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12680,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12680,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12680,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12680,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12680,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12680,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12680,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12680,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12680,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12680,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12680,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12680,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12680,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12680,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12680,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12680,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12680,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12680,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12680,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12680,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12680,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12680,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12680,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12680,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12680,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12680,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12680,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12680,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12680,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12680,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12680,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12680,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12680,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12680,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12680,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12680,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12680,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12680,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12680,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12680,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12680,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12680,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12680,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12680,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12680,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12680,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12680,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12680,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12680,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12680,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12680,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12680,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12680,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12680,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12680,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12680,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12680,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12680,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12680,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12680,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12680,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12680,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12680,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12680,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12680,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12680,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12680,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12680,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12680,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12680,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12680,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12680,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12680,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12680,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12680,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12680,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12680,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12680,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12680,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12680,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12680,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12680,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12680,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12680,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12680,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12680,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12680 : FrameRepair 12680 scalarRow12680 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12680Cells j).1 (repair12680Cells j).2.1
  endpoint_upper := fun j => ((repair12680Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12680Cells j).2.2

theorem repair12681Cells (j : Fin 43) :
    0 ≤ (scalarRow12681.table (sourceIndex j)).upper ∧
    (scalarRow12681.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12681.table (sourceIndex j)).centre) /
      (scalarRow12681.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12681.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12681,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12681,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12681,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12681,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12681,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12681,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12681,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12681,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12681,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12681,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12681,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12681,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12681,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12681,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12681,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12681,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12681,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12681,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12681,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12681,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12681,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12681,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12681,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12681,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12681,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12681,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12681,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12681,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12681,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12681,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12681,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12681,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12681,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12681,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12681,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12681,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12681,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12681,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12681,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12681,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12681,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12681,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12681,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12681,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12681,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12681,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12681,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12681,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12681,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12681,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12681,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12681,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12681,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12681,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12681,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12681,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12681,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12681,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12681,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12681,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12681,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12681,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12681,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12681,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12681,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12681,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12681,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12681,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12681,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12681,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12681,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12681,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12681,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12681,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12681,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12681,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12681,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12681,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12681,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12681,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12681,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12681,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12681,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12681,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12681,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12681,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12681 : FrameRepair 12681 scalarRow12681 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12681Cells j).1 (repair12681Cells j).2.1
  endpoint_upper := fun j => ((repair12681Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12681Cells j).2.2

theorem repair12682Cells (j : Fin 43) :
    0 ≤ (scalarRow12682.table (sourceIndex j)).upper ∧
    (scalarRow12682.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12682.table (sourceIndex j)).centre) /
      (scalarRow12682.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12682.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12682,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12682,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12682,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12682,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12682,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12682,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12682,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12682,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12682,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12682,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12682,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12682,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12682,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12682,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12682,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12682,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12682,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12682,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12682,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12682,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12682,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12682,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12682,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12682,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12682,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12682,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12682,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12682,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12682,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12682,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12682,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12682,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12682,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12682,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12682,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12682,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12682,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12682,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12682,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12682,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12682,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12682,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12682,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12682,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12682,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12682,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12682,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12682,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12682,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12682,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12682,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12682,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12682,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12682,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12682,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12682,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12682,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12682,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12682,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12682,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12682,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12682,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12682,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12682,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12682,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12682,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12682,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12682,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12682,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12682,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12682,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12682,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12682,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12682,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12682,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12682,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12682,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12682,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12682,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12682,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12682,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12682,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12682,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12682,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12682,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12682,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12682 : FrameRepair 12682 scalarRow12682 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12682Cells j).1 (repair12682Cells j).2.1
  endpoint_upper := fun j => ((repair12682Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12682Cells j).2.2

theorem repair12683Cells (j : Fin 43) :
    0 ≤ (scalarRow12683.table (sourceIndex j)).upper ∧
    (scalarRow12683.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12683.table (sourceIndex j)).centre) /
      (scalarRow12683.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12683.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12683,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12683,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12683,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12683,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12683,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12683,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12683,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12683,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12683,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12683,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12683,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12683,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12683,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12683,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12683,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12683,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12683,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12683,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12683,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12683,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12683,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12683,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12683,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12683,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12683,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12683,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12683,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12683,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12683,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12683,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12683,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12683,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12683,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12683,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12683,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12683,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12683,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12683,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12683,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12683,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12683,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12683,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12683,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12683,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12683,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12683,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12683,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12683,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12683,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12683,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12683,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12683,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12683,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12683,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12683,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12683,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12683,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12683,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12683,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12683,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12683,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12683,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12683,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12683,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12683,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12683,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12683,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12683,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12683,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12683,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12683,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12683,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12683,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12683,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12683,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12683,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12683,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12683,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12683,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12683,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12683,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12683,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12683,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12683,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12683,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12683,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12683 : FrameRepair 12683 scalarRow12683 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12683Cells j).1 (repair12683Cells j).2.1
  endpoint_upper := fun j => ((repair12683Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12683Cells j).2.2

theorem repair12684Cells (j : Fin 43) :
    0 ≤ (scalarRow12684.table (sourceIndex j)).upper ∧
    (scalarRow12684.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12684.table (sourceIndex j)).centre) /
      (scalarRow12684.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12684.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12684,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12684,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12684,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12684,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12684,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12684,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12684,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12684,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12684,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12684,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12684,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12684,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12684,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12684,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12684,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12684,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12684,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12684,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12684,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12684,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12684,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12684,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12684,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12684,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12684,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12684,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12684,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12684,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12684,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12684,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12684,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12684,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12684,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12684,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12684,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12684,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12684,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12684,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12684,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12684,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12684,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12684,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12684,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12684,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12684,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12684,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12684,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12684,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12684,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12684,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12684,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12684,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12684,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12684,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12684,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12684,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12684,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12684,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12684,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12684,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12684,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12684,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12684,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12684,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12684,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12684,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12684,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12684,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12684,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12684,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12684,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12684,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12684,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12684,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12684,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12684,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12684,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12684,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12684,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12684,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12684,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12684,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12684,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12684,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12684,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12684,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12684 : FrameRepair 12684 scalarRow12684 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12684Cells j).1 (repair12684Cells j).2.1
  endpoint_upper := fun j => ((repair12684Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12684Cells j).2.2

theorem repair12685Cells (j : Fin 43) :
    0 ≤ (scalarRow12685.table (sourceIndex j)).upper ∧
    (scalarRow12685.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12685.table (sourceIndex j)).centre) /
      (scalarRow12685.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12685.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12685,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12685,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12685,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12685,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12685,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12685,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12685,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12685,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12685,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12685,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12685,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12685,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12685,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12685,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12685,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12685,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12685,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12685,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12685,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12685,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12685,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12685,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12685,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12685,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12685,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12685,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12685,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12685,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12685,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12685,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12685,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12685,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12685,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12685,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12685,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12685,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12685,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12685,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12685,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12685,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12685,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12685,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12685,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12685,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12685,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12685,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12685,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12685,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12685,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12685,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12685,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12685,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12685,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12685,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12685,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12685,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12685,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12685,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12685,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12685,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12685,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12685,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12685,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12685,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12685,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12685,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12685,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12685,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12685,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12685,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12685,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12685,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12685,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12685,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12685,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12685,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12685,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12685,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12685,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12685,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12685,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12685,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12685,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12685,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12685,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12685,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12685 : FrameRepair 12685 scalarRow12685 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12685Cells j).1 (repair12685Cells j).2.1
  endpoint_upper := fun j => ((repair12685Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12685Cells j).2.2

theorem repair12686Cells (j : Fin 43) :
    0 ≤ (scalarRow12686.table (sourceIndex j)).upper ∧
    (scalarRow12686.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12686.table (sourceIndex j)).centre) /
      (scalarRow12686.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12686.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12686,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12686,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12686,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12686,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12686,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12686,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12686,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12686,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12686,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12686,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12686,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12686,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12686,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12686,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12686,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12686,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12686,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12686,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12686,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12686,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12686,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12686,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12686,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12686,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12686,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12686,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12686,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12686,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12686,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12686,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12686,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12686,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12686,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12686,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12686,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12686,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12686,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12686,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12686,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12686,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12686,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12686,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12686,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12686,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12686,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12686,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12686,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12686,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12686,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12686,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12686,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12686,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12686,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12686,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12686,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12686,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12686,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12686,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12686,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12686,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12686,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12686,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12686,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12686,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12686,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12686,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12686,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12686,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12686,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12686,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12686,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12686,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12686,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12686,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12686,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12686,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12686,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12686,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12686,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12686,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12686,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12686,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12686,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12686,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12686,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12686,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12686 : FrameRepair 12686 scalarRow12686 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12686Cells j).1 (repair12686Cells j).2.1
  endpoint_upper := fun j => ((repair12686Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12686Cells j).2.2

theorem repair12687Cells (j : Fin 43) :
    0 ≤ (scalarRow12687.table (sourceIndex j)).upper ∧
    (scalarRow12687.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12687.table (sourceIndex j)).centre) /
      (scalarRow12687.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12687.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12687,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12687,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12687,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12687,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12687,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12687,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12687,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12687,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12687,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12687,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12687,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12687,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12687,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12687,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12687,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12687,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12687,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12687,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12687,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12687,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12687,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12687,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12687,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12687,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12687,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12687,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12687,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12687,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12687,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12687,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12687,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12687,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12687,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12687,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12687,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12687,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12687,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12687,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12687,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12687,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12687,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12687,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12687,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12687,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12687,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12687,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12687,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12687,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12687,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12687,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12687,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12687,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12687,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12687,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12687,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12687,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12687,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12687,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12687,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12687,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12687,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12687,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12687,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12687,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12687,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12687,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12687,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12687,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12687,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12687,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12687,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12687,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12687,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12687,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12687,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12687,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12687,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12687,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12687,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12687,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12687,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12687,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12687,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12687,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12687,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12687,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12687 : FrameRepair 12687 scalarRow12687 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12687Cells j).1 (repair12687Cells j).2.1
  endpoint_upper := fun j => ((repair12687Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12687Cells j).2.2

theorem repair12688Cells (j : Fin 43) :
    0 ≤ (scalarRow12688.table (sourceIndex j)).upper ∧
    (scalarRow12688.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12688.table (sourceIndex j)).centre) /
      (scalarRow12688.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12688.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12688,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12688,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12688,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12688,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12688,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12688,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12688,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12688,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12688,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12688,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12688,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12688,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12688,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12688,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12688,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12688,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12688,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12688,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12688,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12688,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12688,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12688,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12688,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12688,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12688,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12688,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12688,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12688,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12688,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12688,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12688,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12688,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12688,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12688,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12688,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12688,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12688,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12688,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12688,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12688,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12688,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12688,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12688,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12688,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12688,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12688,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12688,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12688,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12688,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12688,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12688,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12688,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12688,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12688,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12688,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12688,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12688,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12688,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12688,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12688,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12688,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12688,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12688,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12688,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12688,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12688,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12688,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12688,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12688,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12688,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12688,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12688,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12688,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12688,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12688,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12688,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12688,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12688,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12688,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12688,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12688,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12688,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12688,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12688,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12688,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12688,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12688 : FrameRepair 12688 scalarRow12688 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12688Cells j).1 (repair12688Cells j).2.1
  endpoint_upper := fun j => ((repair12688Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12688Cells j).2.2

theorem repair12689Cells (j : Fin 43) :
    0 ≤ (scalarRow12689.table (sourceIndex j)).upper ∧
    (scalarRow12689.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12689.table (sourceIndex j)).centre) /
      (scalarRow12689.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12689.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12689,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12689,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12689,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12689,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12689,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12689,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12689,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12689,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12689,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12689,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12689,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12689,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12689,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12689,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12689,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12689,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12689,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12689,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12689,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12689,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12689,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12689,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12689,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12689,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12689,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12689,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12689,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12689,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12689,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12689,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12689,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12689,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12689,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12689,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12689,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12689,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12689,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12689,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12689,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12689,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12689,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12689,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12689,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12689,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12689,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12689,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12689,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12689,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12689,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12689,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12689,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12689,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12689,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12689,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12689,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12689,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12689,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12689,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12689,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12689,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12689,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12689,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12689,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12689,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12689,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12689,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12689,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12689,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12689,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12689,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12689,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12689,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12689,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12689,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12689,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12689,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12689,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12689,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12689,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12689,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12689,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12689,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12689,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12689,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12689,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12689,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12689 : FrameRepair 12689 scalarRow12689 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12689Cells j).1 (repair12689Cells j).2.1
  endpoint_upper := fun j => ((repair12689Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12689Cells j).2.2

theorem repair12690Cells (j : Fin 43) :
    0 ≤ (scalarRow12690.table (sourceIndex j)).upper ∧
    (scalarRow12690.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12690.table (sourceIndex j)).centre) /
      (scalarRow12690.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12690.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12690,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12690,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12690,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12690,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12690,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12690,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12690,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12690,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12690,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12690,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12690,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12690,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12690,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12690,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12690,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12690,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12690,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12690,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12690,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12690,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12690,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12690,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12690,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12690,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12690,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12690,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12690,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12690,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12690,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12690,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12690,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12690,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12690,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12690,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12690,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12690,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12690,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12690,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12690,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12690,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12690,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12690,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12690,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12690,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12690,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12690,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12690,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12690,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12690,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12690,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12690,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12690,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12690,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12690,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12690,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12690,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12690,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12690,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12690,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12690,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12690,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12690,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12690,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12690,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12690,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12690,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12690,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12690,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12690,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12690,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12690,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12690,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12690,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12690,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12690,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12690,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12690,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12690,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12690,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12690,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12690,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12690,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12690,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12690,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12690,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12690,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12690 : FrameRepair 12690 scalarRow12690 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12690Cells j).1 (repair12690Cells j).2.1
  endpoint_upper := fun j => ((repair12690Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12690Cells j).2.2

theorem repair12691Cells (j : Fin 43) :
    0 ≤ (scalarRow12691.table (sourceIndex j)).upper ∧
    (scalarRow12691.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12691.table (sourceIndex j)).centre) /
      (scalarRow12691.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12691.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12691,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12691,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12691,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12691,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12691,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12691,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12691,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12691,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12691,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12691,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12691,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12691,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12691,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12691,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12691,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12691,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12691,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12691,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12691,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12691,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12691,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12691,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12691,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12691,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12691,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12691,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12691,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12691,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12691,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12691,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12691,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12691,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12691,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12691,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12691,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12691,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12691,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12691,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12691,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12691,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12691,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12691,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12691,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12691,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12691,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12691,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12691,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12691,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12691,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12691,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12691,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12691,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12691,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12691,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12691,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12691,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12691,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12691,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12691,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12691,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12691,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12691,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12691,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12691,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12691,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12691,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12691,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12691,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12691,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12691,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12691,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12691,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12691,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12691,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12691,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12691,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12691,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12691,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12691,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12691,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12691,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12691,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12691,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12691,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12691,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12691,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12691 : FrameRepair 12691 scalarRow12691 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12691Cells j).1 (repair12691Cells j).2.1
  endpoint_upper := fun j => ((repair12691Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12691Cells j).2.2

theorem repair12692Cells (j : Fin 43) :
    0 ≤ (scalarRow12692.table (sourceIndex j)).upper ∧
    (scalarRow12692.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12692.table (sourceIndex j)).centre) /
      (scalarRow12692.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12692.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12692,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12692,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12692,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12692,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12692,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12692,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12692,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12692,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12692,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12692,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12692,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12692,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12692,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12692,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12692,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12692,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12692,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12692,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12692,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12692,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12692,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12692,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12692,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12692,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12692,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12692,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12692,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12692,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12692,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12692,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12692,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12692,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12692,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12692,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12692,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12692,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12692,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12692,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12692,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12692,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12692,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12692,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12692,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12692,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12692,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12692,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12692,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12692,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12692,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12692,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12692,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12692,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12692,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12692,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12692,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12692,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12692,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12692,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12692,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12692,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12692,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12692,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12692,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12692,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12692,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12692,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12692,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12692,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12692,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12692,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12692,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12692,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12692,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12692,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12692,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12692,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12692,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12692,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12692,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12692,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12692,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12692,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12692,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12692,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12692,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12692,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12692 : FrameRepair 12692 scalarRow12692 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12692Cells j).1 (repair12692Cells j).2.1
  endpoint_upper := fun j => ((repair12692Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12692Cells j).2.2

theorem repair12693Cells (j : Fin 43) :
    0 ≤ (scalarRow12693.table (sourceIndex j)).upper ∧
    (scalarRow12693.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12693.table (sourceIndex j)).centre) /
      (scalarRow12693.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12693.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12693,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12693,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12693,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12693,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12693,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12693,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12693,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12693,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12693,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12693,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12693,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12693,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12693,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12693,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12693,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12693,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12693,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12693,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12693,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12693,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12693,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12693,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12693,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12693,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12693,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12693,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12693,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12693,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12693,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12693,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12693,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12693,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12693,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12693,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12693,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12693,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12693,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12693,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12693,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12693,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12693,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12693,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12693,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12693,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12693,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12693,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12693,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12693,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12693,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12693,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12693,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12693,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12693,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12693,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12693,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12693,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12693,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12693,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12693,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12693,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12693,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12693,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12693,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12693,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12693,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12693,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12693,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12693,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12693,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12693,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12693,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12693,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12693,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12693,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12693,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12693,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12693,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12693,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12693,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12693,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12693,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12693,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12693,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12693,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12693,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12693,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12693 : FrameRepair 12693 scalarRow12693 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12693Cells j).1 (repair12693Cells j).2.1
  endpoint_upper := fun j => ((repair12693Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12693Cells j).2.2

theorem repair12694Cells (j : Fin 43) :
    0 ≤ (scalarRow12694.table (sourceIndex j)).upper ∧
    (scalarRow12694.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12694.table (sourceIndex j)).centre) /
      (scalarRow12694.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12694.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12694,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12694,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12694,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12694,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12694,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12694,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12694,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12694,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12694,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12694,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12694,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12694,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12694,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12694,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12694,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12694,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12694,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12694,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12694,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12694,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12694,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12694,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12694,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12694,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12694,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12694,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12694,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12694,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12694,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12694,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12694,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12694,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12694,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12694,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12694,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12694,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12694,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12694,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12694,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12694,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12694,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12694,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12694,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12694,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12694,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12694,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12694,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12694,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12694,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12694,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12694,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12694,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12694,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12694,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12694,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12694,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12694,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12694,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12694,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12694,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12694,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12694,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12694,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12694,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12694,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12694,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12694,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12694,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12694,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12694,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12694,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12694,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12694,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12694,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12694,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12694,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12694,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12694,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12694,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12694,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12694,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12694,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12694,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12694,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12694,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12694,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12694 : FrameRepair 12694 scalarRow12694 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12694Cells j).1 (repair12694Cells j).2.1
  endpoint_upper := fun j => ((repair12694Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12694Cells j).2.2

theorem repair12695Cells (j : Fin 43) :
    0 ≤ (scalarRow12695.table (sourceIndex j)).upper ∧
    (scalarRow12695.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12695.table (sourceIndex j)).centre) /
      (scalarRow12695.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12695.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12695,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12695,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12695,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12695,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12695,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12695,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12695,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12695,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12695,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12695,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12695,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12695,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12695,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12695,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12695,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12695,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12695,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12695,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12695,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12695,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12695,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12695,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12695,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12695,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12695,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12695,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12695,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12695,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12695,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12695,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12695,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12695,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12695,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12695,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12695,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12695,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12695,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12695,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12695,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12695,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12695,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12695,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12695,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12695,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12695,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12695,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12695,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12695,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12695,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12695,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12695,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12695,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12695,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12695,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12695,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12695,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12695,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12695,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12695,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12695,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12695,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12695,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12695,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12695,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12695,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12695,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12695,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12695,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12695,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12695,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12695,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12695,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12695,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12695,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12695,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12695,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12695,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12695,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12695,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12695,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12695,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12695,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12695,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12695,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12695,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12695,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12695 : FrameRepair 12695 scalarRow12695 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12695Cells j).1 (repair12695Cells j).2.1
  endpoint_upper := fun j => ((repair12695Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12695Cells j).2.2

theorem repair12696Cells (j : Fin 43) :
    0 ≤ (scalarRow12696.table (sourceIndex j)).upper ∧
    (scalarRow12696.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12696.table (sourceIndex j)).centre) /
      (scalarRow12696.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12696.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12696,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12696,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12696,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12696,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12696,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12696,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12696,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12696,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12696,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12696,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12696,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12696,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12696,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12696,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12696,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12696,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12696,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12696,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12696,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12696,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12696,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12696,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12696,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12696,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12696,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12696,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12696,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12696,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12696,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12696,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12696,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12696,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12696,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12696,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12696,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12696,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12696,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12696,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12696,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12696,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12696,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12696,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12696,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12696,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12696,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12696,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12696,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12696,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12696,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12696,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12696,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12696,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12696,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12696,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12696,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12696,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12696,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12696,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12696,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12696,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12696,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12696,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12696,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12696,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12696,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12696,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12696,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12696,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12696,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12696,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12696,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12696,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12696,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12696,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12696,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12696,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12696,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12696,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12696,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12696,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12696,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12696,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12696,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12696,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12696,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12696,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12696 : FrameRepair 12696 scalarRow12696 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12696Cells j).1 (repair12696Cells j).2.1
  endpoint_upper := fun j => ((repair12696Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12696Cells j).2.2

theorem repair12697Cells (j : Fin 43) :
    0 ≤ (scalarRow12697.table (sourceIndex j)).upper ∧
    (scalarRow12697.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12697.table (sourceIndex j)).centre) /
      (scalarRow12697.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12697.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12697,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12697,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12697,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12697,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12697,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12697,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12697,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12697,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12697,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12697,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12697,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12697,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12697,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12697,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12697,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12697,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12697,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12697,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12697,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12697,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12697,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12697,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12697,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12697,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12697,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12697,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12697,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12697,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12697,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12697,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12697,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12697,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12697,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12697,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12697,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12697,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12697,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12697,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12697,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12697,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12697,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12697,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12697,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12697,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12697,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12697,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12697,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12697,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12697,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12697,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12697,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12697,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12697,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12697,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12697,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12697,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12697,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12697,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12697,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12697,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12697,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12697,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12697,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12697,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12697,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12697,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12697,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12697,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12697,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12697,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12697,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12697,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12697,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12697,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12697,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12697,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12697,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12697,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12697,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12697,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12697,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12697,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12697,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12697,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12697,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12697,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12697 : FrameRepair 12697 scalarRow12697 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12697Cells j).1 (repair12697Cells j).2.1
  endpoint_upper := fun j => ((repair12697Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12697Cells j).2.2

theorem repair12698Cells (j : Fin 43) :
    0 ≤ (scalarRow12698.table (sourceIndex j)).upper ∧
    (scalarRow12698.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12698.table (sourceIndex j)).centre) /
      (scalarRow12698.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12698.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12698,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12698,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12698,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12698,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12698,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12698,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12698,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12698,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12698,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12698,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12698,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12698,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12698,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12698,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12698,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12698,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12698,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12698,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12698,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12698,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12698,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12698,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12698,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12698,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12698,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12698,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12698,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12698,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12698,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12698,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12698,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12698,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12698,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12698,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12698,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12698,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12698,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12698,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12698,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12698,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12698,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12698,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12698,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12698,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12698,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12698,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12698,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12698,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12698,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12698,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12698,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12698,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12698,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12698,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12698,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12698,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12698,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12698,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12698,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12698,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12698,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12698,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12698,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12698,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12698,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12698,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12698,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12698,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12698,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12698,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12698,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12698,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12698,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12698,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12698,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12698,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12698,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12698,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12698,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12698,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12698,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12698,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12698,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12698,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12698,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12698,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12698 : FrameRepair 12698 scalarRow12698 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12698Cells j).1 (repair12698Cells j).2.1
  endpoint_upper := fun j => ((repair12698Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12698Cells j).2.2

theorem repair12699Cells (j : Fin 43) :
    0 ≤ (scalarRow12699.table (sourceIndex j)).upper ∧
    (scalarRow12699.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12699.table (sourceIndex j)).centre) /
      (scalarRow12699.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12699.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12699,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12699,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12699,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12699,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12699,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12699,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12699,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12699,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12699,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12699,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12699,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12699,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12699,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12699,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12699,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12699,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12699,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12699,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12699,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12699,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12699,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12699,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12699,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12699,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12699,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12699,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12699,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12699,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12699,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12699,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12699,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12699,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12699,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12699,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12699,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12699,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12699,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12699,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12699,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12699,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12699,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12699,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12699,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12699,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12699,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12699,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12699,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12699,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12699,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12699,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12699,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12699,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12699,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12699,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12699,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12699,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12699,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12699,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12699,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12699,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12699,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12699,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12699,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12699,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12699,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12699,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12699,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12699,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12699,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12699,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12699,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12699,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12699,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12699,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12699,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12699,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12699,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12699,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12699,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12699,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12699,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12699,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12699,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12699,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12699,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12699,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12699 : FrameRepair 12699 scalarRow12699 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12699Cells j).1 (repair12699Cells j).2.1
  endpoint_upper := fun j => ((repair12699Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12699Cells j).2.2

end BstLean.Part269
