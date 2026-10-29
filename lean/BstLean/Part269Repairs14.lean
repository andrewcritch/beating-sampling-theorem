import BstLean.Part269Rows14
import BstLean.Part269RepairCommon
namespace BstLean.Part269
open Real Set BstLean.Part255 BstLean.Part263 BstLean.Part264
theorem repair12700Cells (j : Fin 43) :
    0 ≤ (scalarRow12700.table (sourceIndex j)).upper ∧
    (scalarRow12700.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12700.table (sourceIndex j)).centre) /
      (scalarRow12700.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12700.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12700,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12700,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12700,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12700,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12700,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12700,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12700,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12700,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12700,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12700,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12700,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12700,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12700,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12700,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12700,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12700,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12700,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12700,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12700,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12700,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12700,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12700,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12700,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12700,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12700,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12700,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12700,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12700,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12700,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12700,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12700,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12700,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12700,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12700,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12700,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12700,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12700,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12700,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12700,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12700,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12700,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12700,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12700,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12700,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12700,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12700,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12700,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12700,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12700,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12700,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12700,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12700,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12700,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12700,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12700,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12700,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12700,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12700,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12700,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12700,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12700,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12700,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12700,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12700,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12700,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12700,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12700,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12700,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12700,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12700,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12700,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12700,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12700,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12700,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12700,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12700,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12700,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12700,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12700,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12700,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12700,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12700,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12700,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12700,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12700,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12700,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12700 : FrameRepair 12700 scalarRow12700 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12700Cells j).1 (repair12700Cells j).2.1
  endpoint_upper := fun j => ((repair12700Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12700Cells j).2.2

theorem repair12701Cells (j : Fin 43) :
    0 ≤ (scalarRow12701.table (sourceIndex j)).upper ∧
    (scalarRow12701.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12701.table (sourceIndex j)).centre) /
      (scalarRow12701.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12701.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12701,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12701,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12701,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12701,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12701,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12701,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12701,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12701,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12701,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12701,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12701,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12701,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12701,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12701,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12701,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12701,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12701,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12701,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12701,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12701,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12701,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12701,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12701,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12701,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12701,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12701,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12701,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12701,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12701,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12701,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12701,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12701,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12701,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12701,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12701,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12701,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12701,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12701,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12701,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12701,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12701,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12701,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12701,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12701,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12701,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12701,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12701,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12701,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12701,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12701,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12701,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12701,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12701,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12701,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12701,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12701,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12701,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12701,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12701,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12701,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12701,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12701,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12701,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12701,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12701,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12701,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12701,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12701,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12701,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12701,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12701,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12701,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12701,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12701,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12701,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12701,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12701,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12701,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12701,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12701,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12701,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12701,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12701,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12701,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12701,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12701,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12701 : FrameRepair 12701 scalarRow12701 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12701Cells j).1 (repair12701Cells j).2.1
  endpoint_upper := fun j => ((repair12701Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12701Cells j).2.2

theorem repair12702Cells (j : Fin 43) :
    0 ≤ (scalarRow12702.table (sourceIndex j)).upper ∧
    (scalarRow12702.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12702.table (sourceIndex j)).centre) /
      (scalarRow12702.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12702.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12702,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12702,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12702,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12702,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12702,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12702,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12702,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12702,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12702,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12702,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12702,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12702,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12702,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12702,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12702,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12702,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12702,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12702,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12702,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12702,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12702,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12702,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12702,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12702,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12702,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12702,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12702,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12702,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12702,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12702,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12702,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12702,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12702,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12702,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12702,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12702,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12702,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12702,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12702,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12702,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12702,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12702,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12702,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12702,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12702,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12702,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12702,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12702,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12702,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12702,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12702,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12702,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12702,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12702,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12702,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12702,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12702,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12702,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12702,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12702,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12702,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12702,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12702,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12702,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12702,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12702,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12702,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12702,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12702,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12702,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12702,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12702,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12702,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12702,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12702,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12702,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12702,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12702,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12702,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12702,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12702,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12702,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12702,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12702,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12702,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12702,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12702 : FrameRepair 12702 scalarRow12702 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12702Cells j).1 (repair12702Cells j).2.1
  endpoint_upper := fun j => ((repair12702Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12702Cells j).2.2

theorem repair12703Cells (j : Fin 43) :
    0 ≤ (scalarRow12703.table (sourceIndex j)).upper ∧
    (scalarRow12703.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12703.table (sourceIndex j)).centre) /
      (scalarRow12703.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12703.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12703,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12703,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12703,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12703,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12703,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12703,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12703,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12703,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12703,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12703,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12703,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12703,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12703,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12703,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12703,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12703,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12703,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12703,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12703,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12703,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12703,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12703,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12703,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12703,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12703,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12703,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12703,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12703,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12703,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12703,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12703,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12703,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12703,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12703,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12703,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12703,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12703,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12703,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12703,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12703,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12703,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12703,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12703,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12703,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12703,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12703,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12703,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12703,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12703,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12703,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12703,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12703,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12703,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12703,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12703,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12703,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12703,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12703,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12703,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12703,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12703,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12703,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12703,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12703,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12703,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12703,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12703,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12703,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12703,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12703,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12703,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12703,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12703,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12703,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12703,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12703,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12703,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12703,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12703,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12703,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12703,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12703,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12703,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12703,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12703,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12703,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12703 : FrameRepair 12703 scalarRow12703 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12703Cells j).1 (repair12703Cells j).2.1
  endpoint_upper := fun j => ((repair12703Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12703Cells j).2.2

theorem repair12704Cells (j : Fin 43) :
    0 ≤ (scalarRow12704.table (sourceIndex j)).upper ∧
    (scalarRow12704.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12704.table (sourceIndex j)).centre) /
      (scalarRow12704.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12704.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12704,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12704,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12704,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12704,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12704,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12704,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12704,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12704,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12704,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12704,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12704,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12704,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12704,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12704,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12704,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12704,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12704,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12704,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12704,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12704,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12704,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12704,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12704,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12704,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12704,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12704,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12704,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12704,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12704,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12704,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12704,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12704,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12704,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12704,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12704,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12704,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12704,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12704,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12704,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12704,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12704,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12704,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12704,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12704,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12704,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12704,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12704,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12704,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12704,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12704,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12704,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12704,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12704,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12704,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12704,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12704,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12704,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12704,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12704,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12704,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12704,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12704,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12704,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12704,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12704,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12704,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12704,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12704,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12704,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12704,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12704,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12704,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12704,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12704,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12704,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12704,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12704,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12704,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12704,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12704,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12704,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12704,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12704,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12704,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12704,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12704,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12704 : FrameRepair 12704 scalarRow12704 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12704Cells j).1 (repair12704Cells j).2.1
  endpoint_upper := fun j => ((repair12704Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12704Cells j).2.2

theorem repair12705Cells (j : Fin 43) :
    0 ≤ (scalarRow12705.table (sourceIndex j)).upper ∧
    (scalarRow12705.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12705.table (sourceIndex j)).centre) /
      (scalarRow12705.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12705.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12705,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12705,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12705,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12705,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12705,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12705,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12705,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12705,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12705,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12705,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12705,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12705,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12705,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12705,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12705,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12705,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12705,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12705,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12705,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12705,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12705,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12705,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12705,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12705,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12705,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12705,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12705,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12705,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12705,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12705,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12705,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12705,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12705,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12705,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12705,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12705,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12705,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12705,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12705,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12705,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12705,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12705,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12705,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12705,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12705,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12705,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12705,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12705,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12705,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12705,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12705,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12705,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12705,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12705,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12705,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12705,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12705,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12705,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12705,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12705,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12705,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12705,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12705,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12705,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12705,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12705,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12705,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12705,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12705,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12705,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12705,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12705,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12705,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12705,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12705,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12705,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12705,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12705,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12705,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12705,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12705,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12705,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12705,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12705,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12705,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12705,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12705 : FrameRepair 12705 scalarRow12705 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12705Cells j).1 (repair12705Cells j).2.1
  endpoint_upper := fun j => ((repair12705Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12705Cells j).2.2

theorem repair12706Cells (j : Fin 43) :
    0 ≤ (scalarRow12706.table (sourceIndex j)).upper ∧
    (scalarRow12706.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12706.table (sourceIndex j)).centre) /
      (scalarRow12706.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12706.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12706,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12706,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12706,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12706,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12706,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12706,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12706,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12706,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12706,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12706,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12706,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12706,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12706,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12706,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12706,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12706,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12706,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12706,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12706,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12706,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12706,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12706,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12706,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12706,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12706,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12706,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12706,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12706,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12706,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12706,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12706,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12706,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12706,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12706,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12706,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12706,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12706,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12706,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12706,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12706,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12706,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12706,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12706,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12706,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12706,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12706,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12706,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12706,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12706,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12706,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12706,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12706,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12706,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12706,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12706,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12706,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12706,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12706,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12706,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12706,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12706,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12706,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12706,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12706,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12706,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12706,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12706,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12706,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12706,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12706,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12706,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12706,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12706,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12706,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12706,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12706,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12706,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12706,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12706,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12706,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12706,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12706,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12706,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12706,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12706,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12706,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12706 : FrameRepair 12706 scalarRow12706 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12706Cells j).1 (repair12706Cells j).2.1
  endpoint_upper := fun j => ((repair12706Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12706Cells j).2.2

theorem repair12707Cells (j : Fin 43) :
    0 ≤ (scalarRow12707.table (sourceIndex j)).upper ∧
    (scalarRow12707.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12707.table (sourceIndex j)).centre) /
      (scalarRow12707.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12707.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12707,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12707,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12707,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12707,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12707,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12707,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12707,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12707,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12707,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12707,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12707,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12707,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12707,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12707,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12707,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12707,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12707,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12707,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12707,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12707,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12707,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12707,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12707,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12707,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12707,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12707,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12707,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12707,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12707,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12707,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12707,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12707,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12707,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12707,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12707,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12707,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12707,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12707,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12707,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12707,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12707,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12707,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12707,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12707,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12707,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12707,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12707,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12707,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12707,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12707,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12707,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12707,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12707,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12707,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12707,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12707,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12707,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12707,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12707,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12707,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12707,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12707,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12707,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12707,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12707,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12707,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12707,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12707,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12707,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12707,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12707,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12707,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12707,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12707,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12707,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12707,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12707,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12707,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12707,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12707,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12707,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12707,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12707,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12707,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12707,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12707,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12707 : FrameRepair 12707 scalarRow12707 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12707Cells j).1 (repair12707Cells j).2.1
  endpoint_upper := fun j => ((repair12707Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12707Cells j).2.2

theorem repair12708Cells (j : Fin 43) :
    0 ≤ (scalarRow12708.table (sourceIndex j)).upper ∧
    (scalarRow12708.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12708.table (sourceIndex j)).centre) /
      (scalarRow12708.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12708.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12708,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12708,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12708,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12708,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12708,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12708,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12708,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12708,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12708,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12708,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12708,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12708,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12708,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12708,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12708,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12708,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12708,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12708,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12708,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12708,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12708,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12708,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12708,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12708,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12708,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12708,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12708,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12708,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12708,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12708,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12708,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12708,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12708,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12708,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12708,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12708,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12708,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12708,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12708,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12708,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12708,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12708,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12708,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12708,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12708,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12708,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12708,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12708,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12708,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12708,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12708,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12708,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12708,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12708,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12708,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12708,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12708,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12708,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12708,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12708,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12708,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12708,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12708,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12708,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12708,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12708,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12708,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12708,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12708,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12708,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12708,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12708,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12708,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12708,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12708,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12708,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12708,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12708,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12708,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12708,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12708,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12708,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12708,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12708,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12708,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12708,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12708 : FrameRepair 12708 scalarRow12708 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12708Cells j).1 (repair12708Cells j).2.1
  endpoint_upper := fun j => ((repair12708Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12708Cells j).2.2

theorem repair12709Cells (j : Fin 43) :
    0 ≤ (scalarRow12709.table (sourceIndex j)).upper ∧
    (scalarRow12709.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12709.table (sourceIndex j)).centre) /
      (scalarRow12709.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12709.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12709,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12709,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12709,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12709,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12709,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12709,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12709,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12709,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12709,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12709,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12709,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12709,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12709,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12709,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12709,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12709,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12709,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12709,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12709,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12709,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12709,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12709,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12709,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12709,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12709,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12709,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12709,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12709,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12709,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12709,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12709,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12709,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12709,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12709,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12709,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12709,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12709,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12709,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12709,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12709,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12709,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12709,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12709,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12709,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12709,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12709,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12709,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12709,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12709,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12709,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12709,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12709,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12709,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12709,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12709,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12709,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12709,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12709,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12709,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12709,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12709,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12709,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12709,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12709,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12709,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12709,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12709,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12709,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12709,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12709,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12709,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12709,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12709,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12709,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12709,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12709,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12709,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12709,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12709,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12709,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12709,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12709,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12709,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12709,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12709,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12709,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12709 : FrameRepair 12709 scalarRow12709 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12709Cells j).1 (repair12709Cells j).2.1
  endpoint_upper := fun j => ((repair12709Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12709Cells j).2.2

theorem repair12710Cells (j : Fin 43) :
    0 ≤ (scalarRow12710.table (sourceIndex j)).upper ∧
    (scalarRow12710.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12710.table (sourceIndex j)).centre) /
      (scalarRow12710.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12710.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12710,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12710,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12710,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12710,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12710,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12710,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12710,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12710,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12710,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12710,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12710,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12710,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12710,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12710,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12710,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12710,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12710,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12710,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12710,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12710,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12710,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12710,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12710,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12710,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12710,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12710,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12710,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12710,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12710,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12710,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12710,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12710,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12710,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12710,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12710,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12710,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12710,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12710,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12710,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12710,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12710,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12710,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12710,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12710,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12710,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12710,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12710,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12710,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12710,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12710,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12710,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12710,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12710,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12710,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12710,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12710,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12710,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12710,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12710,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12710,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12710,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12710,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12710,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12710,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12710,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12710,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12710,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12710,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12710,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12710,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12710,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12710,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12710,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12710,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12710,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12710,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12710,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12710,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12710,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12710,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12710,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12710,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12710,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12710,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12710,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12710,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12710 : FrameRepair 12710 scalarRow12710 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12710Cells j).1 (repair12710Cells j).2.1
  endpoint_upper := fun j => ((repair12710Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12710Cells j).2.2

theorem repair12711Cells (j : Fin 43) :
    0 ≤ (scalarRow12711.table (sourceIndex j)).upper ∧
    (scalarRow12711.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12711.table (sourceIndex j)).centre) /
      (scalarRow12711.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12711.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12711,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12711,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12711,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12711,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12711,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12711,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12711,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12711,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12711,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12711,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12711,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12711,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12711,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12711,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12711,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12711,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12711,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12711,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12711,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12711,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12711,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12711,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12711,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12711,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12711,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12711,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12711,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12711,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12711,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12711,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12711,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12711,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12711,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12711,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12711,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12711,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12711,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12711,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12711,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12711,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12711,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12711,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12711,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12711,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12711,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12711,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12711,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12711,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12711,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12711,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12711,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12711,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12711,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12711,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12711,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12711,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12711,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12711,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12711,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12711,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12711,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12711,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12711,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12711,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12711,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12711,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12711,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12711,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12711,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12711,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12711,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12711,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12711,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12711,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12711,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12711,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12711,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12711,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12711,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12711,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12711,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12711,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12711,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12711,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12711,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12711,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12711 : FrameRepair 12711 scalarRow12711 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12711Cells j).1 (repair12711Cells j).2.1
  endpoint_upper := fun j => ((repair12711Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12711Cells j).2.2

theorem repair12712Cells (j : Fin 43) :
    0 ≤ (scalarRow12712.table (sourceIndex j)).upper ∧
    (scalarRow12712.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12712.table (sourceIndex j)).centre) /
      (scalarRow12712.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12712.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12712,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12712,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12712,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12712,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12712,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12712,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12712,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12712,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12712,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12712,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12712,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12712,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12712,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12712,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12712,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12712,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12712,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12712,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12712,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12712,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12712,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12712,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12712,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12712,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12712,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12712,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12712,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12712,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12712,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12712,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12712,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12712,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12712,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12712,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12712,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12712,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12712,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12712,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12712,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12712,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12712,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12712,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12712,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12712,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12712,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12712,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12712,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12712,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12712,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12712,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12712,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12712,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12712,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12712,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12712,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12712,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12712,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12712,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12712,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12712,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12712,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12712,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12712,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12712,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12712,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12712,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12712,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12712,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12712,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12712,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12712,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12712,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12712,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12712,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12712,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12712,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12712,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12712,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12712,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12712,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12712,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12712,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12712,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12712,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12712,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12712,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12712 : FrameRepair 12712 scalarRow12712 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12712Cells j).1 (repair12712Cells j).2.1
  endpoint_upper := fun j => ((repair12712Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12712Cells j).2.2

theorem repair12713Cells (j : Fin 43) :
    0 ≤ (scalarRow12713.table (sourceIndex j)).upper ∧
    (scalarRow12713.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12713.table (sourceIndex j)).centre) /
      (scalarRow12713.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12713.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12713,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12713,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12713,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12713,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12713,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12713,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12713,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12713,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12713,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12713,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12713,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12713,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12713,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12713,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12713,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12713,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12713,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12713,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12713,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12713,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12713,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12713,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12713,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12713,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12713,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12713,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12713,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12713,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12713,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12713,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12713,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12713,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12713,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12713,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12713,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12713,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12713,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12713,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12713,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12713,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12713,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12713,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12713,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12713,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12713,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12713,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12713,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12713,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12713,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12713,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12713,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12713,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12713,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12713,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12713,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12713,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12713,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12713,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12713,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12713,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12713,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12713,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12713,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12713,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12713,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12713,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12713,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12713,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12713,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12713,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12713,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12713,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12713,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12713,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12713,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12713,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12713,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12713,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12713,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12713,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12713,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12713,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12713,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12713,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12713,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12713,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12713 : FrameRepair 12713 scalarRow12713 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12713Cells j).1 (repair12713Cells j).2.1
  endpoint_upper := fun j => ((repair12713Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12713Cells j).2.2

theorem repair12714Cells (j : Fin 43) :
    0 ≤ (scalarRow12714.table (sourceIndex j)).upper ∧
    (scalarRow12714.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12714.table (sourceIndex j)).centre) /
      (scalarRow12714.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12714.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12714,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12714,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12714,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12714,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12714,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12714,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12714,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12714,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12714,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12714,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12714,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12714,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12714,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12714,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12714,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12714,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12714,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12714,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12714,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12714,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12714,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12714,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12714,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12714,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12714,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12714,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12714,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12714,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12714,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12714,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12714,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12714,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12714,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12714,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12714,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12714,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12714,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12714,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12714,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12714,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12714,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12714,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12714,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12714,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12714,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12714,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12714,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12714,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12714,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12714,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12714,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12714,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12714,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12714,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12714,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12714,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12714,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12714,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12714,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12714,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12714,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12714,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12714,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12714,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12714,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12714,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12714,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12714,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12714,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12714,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12714,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12714,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12714,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12714,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12714,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12714,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12714,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12714,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12714,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12714,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12714,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12714,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12714,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12714,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12714,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12714,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12714 : FrameRepair 12714 scalarRow12714 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12714Cells j).1 (repair12714Cells j).2.1
  endpoint_upper := fun j => ((repair12714Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12714Cells j).2.2

theorem repair12715Cells (j : Fin 43) :
    0 ≤ (scalarRow12715.table (sourceIndex j)).upper ∧
    (scalarRow12715.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12715.table (sourceIndex j)).centre) /
      (scalarRow12715.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12715.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12715,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12715,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12715,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12715,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12715,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12715,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12715,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12715,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12715,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12715,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12715,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12715,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12715,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12715,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12715,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12715,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12715,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12715,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12715,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12715,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12715,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12715,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12715,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12715,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12715,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12715,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12715,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12715,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12715,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12715,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12715,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12715,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12715,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12715,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12715,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12715,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12715,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12715,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12715,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12715,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12715,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12715,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12715,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12715,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12715,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12715,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12715,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12715,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12715,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12715,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12715,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12715,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12715,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12715,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12715,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12715,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12715,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12715,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12715,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12715,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12715,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12715,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12715,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12715,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12715,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12715,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12715,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12715,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12715,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12715,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12715,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12715,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12715,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12715,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12715,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12715,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12715,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12715,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12715,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12715,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12715,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12715,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12715,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12715,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12715,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12715,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12715 : FrameRepair 12715 scalarRow12715 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12715Cells j).1 (repair12715Cells j).2.1
  endpoint_upper := fun j => ((repair12715Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12715Cells j).2.2

theorem repair12716Cells (j : Fin 43) :
    0 ≤ (scalarRow12716.table (sourceIndex j)).upper ∧
    (scalarRow12716.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12716.table (sourceIndex j)).centre) /
      (scalarRow12716.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12716.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12716,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12716,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12716,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12716,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12716,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12716,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12716,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12716,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12716,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12716,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12716,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12716,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12716,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12716,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12716,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12716,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12716,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12716,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12716,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12716,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12716,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12716,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12716,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12716,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12716,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12716,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12716,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12716,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12716,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12716,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12716,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12716,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12716,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12716,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12716,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12716,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12716,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12716,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12716,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12716,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12716,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12716,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12716,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12716,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12716,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12716,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12716,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12716,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12716,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12716,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12716,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12716,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12716,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12716,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12716,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12716,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12716,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12716,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12716,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12716,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12716,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12716,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12716,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12716,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12716,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12716,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12716,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12716,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12716,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12716,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12716,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12716,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12716,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12716,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12716,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12716,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12716,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12716,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12716,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12716,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12716,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12716,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12716,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12716,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12716,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12716,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12716 : FrameRepair 12716 scalarRow12716 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12716Cells j).1 (repair12716Cells j).2.1
  endpoint_upper := fun j => ((repair12716Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12716Cells j).2.2

theorem repair12717Cells (j : Fin 43) :
    0 ≤ (scalarRow12717.table (sourceIndex j)).upper ∧
    (scalarRow12717.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12717.table (sourceIndex j)).centre) /
      (scalarRow12717.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12717.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12717,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12717,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12717,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12717,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12717,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12717,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12717,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12717,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12717,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12717,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12717,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12717,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12717,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12717,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12717,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12717,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12717,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12717,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12717,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12717,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12717,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12717,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12717,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12717,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12717,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12717,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12717,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12717,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12717,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12717,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12717,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12717,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12717,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12717,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12717,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12717,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12717,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12717,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12717,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12717,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12717,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12717,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12717,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12717,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12717,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12717,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12717,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12717,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12717,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12717,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12717,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12717,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12717,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12717,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12717,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12717,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12717,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12717,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12717,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12717,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12717,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12717,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12717,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12717,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12717,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12717,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12717,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12717,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12717,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12717,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12717,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12717,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12717,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12717,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12717,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12717,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12717,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12717,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12717,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12717,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12717,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12717,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12717,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12717,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12717,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12717,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12717 : FrameRepair 12717 scalarRow12717 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12717Cells j).1 (repair12717Cells j).2.1
  endpoint_upper := fun j => ((repair12717Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12717Cells j).2.2

theorem repair12718Cells (j : Fin 43) :
    0 ≤ (scalarRow12718.table (sourceIndex j)).upper ∧
    (scalarRow12718.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12718.table (sourceIndex j)).centre) /
      (scalarRow12718.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12718.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12718,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12718,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12718,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12718,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12718,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12718,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12718,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12718,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12718,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12718,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12718,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12718,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12718,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12718,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12718,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12718,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12718,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12718,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12718,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12718,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12718,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12718,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12718,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12718,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12718,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12718,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12718,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12718,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12718,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12718,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12718,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12718,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12718,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12718,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12718,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12718,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12718,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12718,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12718,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12718,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12718,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12718,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12718,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12718,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12718,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12718,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12718,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12718,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12718,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12718,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12718,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12718,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12718,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12718,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12718,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12718,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12718,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12718,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12718,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12718,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12718,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12718,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12718,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12718,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12718,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12718,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12718,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12718,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12718,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12718,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12718,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12718,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12718,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12718,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12718,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12718,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12718,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12718,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12718,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12718,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12718,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12718,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12718,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12718,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12718,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12718,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12718 : FrameRepair 12718 scalarRow12718 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12718Cells j).1 (repair12718Cells j).2.1
  endpoint_upper := fun j => ((repair12718Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12718Cells j).2.2

theorem repair12719Cells (j : Fin 43) :
    0 ≤ (scalarRow12719.table (sourceIndex j)).upper ∧
    (scalarRow12719.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12719.table (sourceIndex j)).centre) /
      (scalarRow12719.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12719.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12719,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12719,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12719,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12719,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12719,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12719,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12719,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12719,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12719,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12719,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12719,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12719,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12719,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12719,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12719,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12719,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12719,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12719,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12719,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12719,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12719,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12719,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12719,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12719,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12719,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12719,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12719,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12719,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12719,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12719,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12719,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12719,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12719,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12719,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12719,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12719,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12719,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12719,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12719,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12719,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12719,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12719,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12719,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12719,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12719,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12719,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12719,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12719,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12719,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12719,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12719,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12719,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12719,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12719,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12719,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12719,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12719,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12719,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12719,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12719,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12719,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12719,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12719,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12719,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12719,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12719,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12719,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12719,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12719,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12719,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12719,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12719,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12719,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12719,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12719,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12719,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12719,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12719,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12719,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12719,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12719,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12719,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12719,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12719,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12719,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12719,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12719 : FrameRepair 12719 scalarRow12719 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12719Cells j).1 (repair12719Cells j).2.1
  endpoint_upper := fun j => ((repair12719Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12719Cells j).2.2

theorem repair12720Cells (j : Fin 43) :
    0 ≤ (scalarRow12720.table (sourceIndex j)).upper ∧
    (scalarRow12720.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12720.table (sourceIndex j)).centre) /
      (scalarRow12720.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12720.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12720,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12720,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12720,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12720,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12720,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12720,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12720,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12720,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12720,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12720,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12720,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12720,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12720,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12720,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12720,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12720,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12720,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12720,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12720,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12720,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12720,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12720,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12720,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12720,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12720,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12720,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12720,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12720,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12720,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12720,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12720,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12720,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12720,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12720,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12720,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12720,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12720,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12720,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12720,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12720,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12720,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12720,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12720,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12720,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12720,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12720,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12720,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12720,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12720,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12720,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12720,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12720,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12720,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12720,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12720,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12720,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12720,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12720,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12720,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12720,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12720,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12720,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12720,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12720,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12720,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12720,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12720,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12720,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12720,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12720,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12720,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12720,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12720,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12720,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12720,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12720,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12720,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12720,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12720,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12720,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12720,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12720,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12720,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12720,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12720,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12720,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12720 : FrameRepair 12720 scalarRow12720 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12720Cells j).1 (repair12720Cells j).2.1
  endpoint_upper := fun j => ((repair12720Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12720Cells j).2.2

theorem repair12721Cells (j : Fin 43) :
    0 ≤ (scalarRow12721.table (sourceIndex j)).upper ∧
    (scalarRow12721.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12721.table (sourceIndex j)).centre) /
      (scalarRow12721.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12721.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12721,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12721,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12721,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12721,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12721,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12721,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12721,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12721,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12721,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12721,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12721,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12721,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12721,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12721,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12721,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12721,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12721,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12721,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12721,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12721,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12721,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12721,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12721,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12721,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12721,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12721,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12721,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12721,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12721,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12721,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12721,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12721,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12721,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12721,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12721,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12721,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12721,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12721,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12721,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12721,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12721,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12721,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12721,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12721,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12721,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12721,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12721,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12721,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12721,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12721,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12721,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12721,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12721,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12721,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12721,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12721,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12721,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12721,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12721,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12721,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12721,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12721,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12721,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12721,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12721,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12721,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12721,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12721,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12721,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12721,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12721,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12721,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12721,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12721,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12721,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12721,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12721,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12721,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12721,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12721,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12721,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12721,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12721,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12721,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12721,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12721,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12721 : FrameRepair 12721 scalarRow12721 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12721Cells j).1 (repair12721Cells j).2.1
  endpoint_upper := fun j => ((repair12721Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12721Cells j).2.2

theorem repair12722Cells (j : Fin 43) :
    0 ≤ (scalarRow12722.table (sourceIndex j)).upper ∧
    (scalarRow12722.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12722.table (sourceIndex j)).centre) /
      (scalarRow12722.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12722.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12722,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12722,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12722,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12722,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12722,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12722,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12722,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12722,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12722,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12722,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12722,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12722,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12722,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12722,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12722,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12722,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12722,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12722,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12722,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12722,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12722,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12722,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12722,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12722,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12722,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12722,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12722,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12722,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12722,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12722,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12722,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12722,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12722,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12722,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12722,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12722,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12722,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12722,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12722,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12722,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12722,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12722,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12722,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12722,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12722,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12722,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12722,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12722,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12722,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12722,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12722,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12722,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12722,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12722,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12722,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12722,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12722,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12722,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12722,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12722,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12722,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12722,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12722,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12722,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12722,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12722,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12722,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12722,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12722,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12722,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12722,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12722,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12722,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12722,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12722,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12722,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12722,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12722,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12722,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12722,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12722,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12722,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12722,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12722,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12722,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12722,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12722 : FrameRepair 12722 scalarRow12722 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12722Cells j).1 (repair12722Cells j).2.1
  endpoint_upper := fun j => ((repair12722Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12722Cells j).2.2

theorem repair12723Cells (j : Fin 43) :
    0 ≤ (scalarRow12723.table (sourceIndex j)).upper ∧
    (scalarRow12723.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12723.table (sourceIndex j)).centre) /
      (scalarRow12723.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12723.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12723,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12723,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12723,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12723,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12723,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12723,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12723,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12723,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12723,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12723,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12723,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12723,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12723,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12723,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12723,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12723,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12723,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12723,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12723,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12723,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12723,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12723,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12723,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12723,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12723,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12723,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12723,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12723,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12723,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12723,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12723,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12723,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12723,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12723,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12723,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12723,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12723,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12723,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12723,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12723,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12723,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12723,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12723,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12723,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12723,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12723,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12723,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12723,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12723,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12723,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12723,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12723,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12723,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12723,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12723,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12723,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12723,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12723,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12723,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12723,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12723,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12723,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12723,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12723,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12723,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12723,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12723,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12723,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12723,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12723,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12723,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12723,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12723,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12723,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12723,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12723,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12723,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12723,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12723,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12723,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12723,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12723,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12723,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12723,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12723,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12723,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12723 : FrameRepair 12723 scalarRow12723 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12723Cells j).1 (repair12723Cells j).2.1
  endpoint_upper := fun j => ((repair12723Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12723Cells j).2.2

theorem repair12724Cells (j : Fin 43) :
    0 ≤ (scalarRow12724.table (sourceIndex j)).upper ∧
    (scalarRow12724.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12724.table (sourceIndex j)).centre) /
      (scalarRow12724.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12724.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12724,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12724,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12724,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12724,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12724,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12724,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12724,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12724,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12724,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12724,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12724,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12724,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12724,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12724,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12724,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12724,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12724,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12724,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12724,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12724,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12724,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12724,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12724,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12724,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12724,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12724,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12724,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12724,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12724,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12724,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12724,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12724,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12724,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12724,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12724,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12724,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12724,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12724,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12724,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12724,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12724,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12724,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12724,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12724,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12724,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12724,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12724,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12724,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12724,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12724,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12724,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12724,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12724,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12724,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12724,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12724,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12724,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12724,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12724,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12724,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12724,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12724,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12724,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12724,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12724,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12724,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12724,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12724,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12724,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12724,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12724,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12724,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12724,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12724,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12724,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12724,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12724,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12724,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12724,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12724,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12724,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12724,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12724,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12724,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12724,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12724,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12724 : FrameRepair 12724 scalarRow12724 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12724Cells j).1 (repair12724Cells j).2.1
  endpoint_upper := fun j => ((repair12724Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12724Cells j).2.2

end BstLean.Part269
