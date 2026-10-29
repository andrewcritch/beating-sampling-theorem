import BstLean.Part269Rows27
import BstLean.Part269RepairCommon
namespace BstLean.Part269
open Real Set BstLean.Part255 BstLean.Part263 BstLean.Part264
theorem repair13025Cells (j : Fin 43) :
    0 ≤ (scalarRow13025.table (sourceIndex j)).upper ∧
    (scalarRow13025.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13025.table (sourceIndex j)).centre) /
      (scalarRow13025.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13025.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13025,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13025,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13025,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13025,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13025,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13025,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13025,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13025,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13025,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13025,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13025,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13025,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13025,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13025,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13025,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13025,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13025,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13025,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13025,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13025,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13025,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13025,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13025,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13025,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13025,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13025,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13025,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13025,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13025,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13025,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13025,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13025,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13025,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13025,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13025,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13025,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13025,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13025,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13025,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13025,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13025,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13025,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13025,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13025,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13025,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13025,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13025,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13025,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13025,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13025,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13025,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13025,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13025,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13025,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13025,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13025,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13025,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13025,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13025,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13025,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13025,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13025,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13025,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13025,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13025,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13025,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13025,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13025,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13025,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13025,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13025,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13025,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13025,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13025,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13025,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13025,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13025,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13025,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13025,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13025,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13025,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13025,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13025,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13025,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13025,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13025,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13025 : FrameRepair 13025 scalarRow13025 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13025Cells j).1 (repair13025Cells j).2.1
  endpoint_upper := fun j => ((repair13025Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13025Cells j).2.2

theorem repair13026Cells (j : Fin 43) :
    0 ≤ (scalarRow13026.table (sourceIndex j)).upper ∧
    (scalarRow13026.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13026.table (sourceIndex j)).centre) /
      (scalarRow13026.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13026.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13026,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13026,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13026,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13026,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13026,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13026,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13026,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13026,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13026,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13026,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13026,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13026,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13026,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13026,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13026,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13026,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13026,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13026,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13026,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13026,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13026,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13026,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13026,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13026,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13026,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13026,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13026,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13026,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13026,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13026,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13026,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13026,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13026,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13026,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13026,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13026,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13026,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13026,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13026,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13026,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13026,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13026,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13026,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13026,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13026,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13026,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13026,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13026,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13026,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13026,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13026,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13026,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13026,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13026,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13026,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13026,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13026,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13026,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13026,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13026,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13026,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13026,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13026,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13026,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13026,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13026,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13026,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13026,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13026,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13026,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13026,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13026,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13026,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13026,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13026,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13026,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13026,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13026,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13026,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13026,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13026,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13026,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13026,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13026,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13026,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13026,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13026 : FrameRepair 13026 scalarRow13026 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13026Cells j).1 (repair13026Cells j).2.1
  endpoint_upper := fun j => ((repair13026Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13026Cells j).2.2

theorem repair13027Cells (j : Fin 43) :
    0 ≤ (scalarRow13027.table (sourceIndex j)).upper ∧
    (scalarRow13027.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13027.table (sourceIndex j)).centre) /
      (scalarRow13027.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13027.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13027,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13027,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13027,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13027,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13027,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13027,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13027,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13027,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13027,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13027,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13027,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13027,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13027,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13027,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13027,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13027,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13027,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13027,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13027,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13027,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13027,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13027,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13027,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13027,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13027,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13027,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13027,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13027,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13027,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13027,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13027,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13027,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13027,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13027,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13027,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13027,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13027,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13027,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13027,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13027,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13027,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13027,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13027,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13027,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13027,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13027,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13027,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13027,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13027,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13027,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13027,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13027,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13027,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13027,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13027,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13027,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13027,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13027,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13027,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13027,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13027,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13027,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13027,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13027,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13027,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13027,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13027,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13027,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13027,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13027,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13027,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13027,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13027,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13027,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13027,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13027,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13027,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13027,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13027,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13027,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13027,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13027,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13027,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13027,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13027,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13027,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13027 : FrameRepair 13027 scalarRow13027 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13027Cells j).1 (repair13027Cells j).2.1
  endpoint_upper := fun j => ((repair13027Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13027Cells j).2.2

theorem repair13028Cells (j : Fin 43) :
    0 ≤ (scalarRow13028.table (sourceIndex j)).upper ∧
    (scalarRow13028.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13028.table (sourceIndex j)).centre) /
      (scalarRow13028.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13028.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13028,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13028,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13028,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13028,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13028,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13028,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13028,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13028,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13028,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13028,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13028,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13028,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13028,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13028,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13028,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13028,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13028,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13028,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13028,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13028,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13028,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13028,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13028,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13028,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13028,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13028,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13028,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13028,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13028,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13028,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13028,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13028,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13028,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13028,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13028,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13028,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13028,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13028,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13028,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13028,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13028,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13028,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13028,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13028,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13028,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13028,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13028,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13028,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13028,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13028,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13028,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13028,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13028,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13028,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13028,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13028,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13028,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13028,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13028,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13028,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13028,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13028,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13028,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13028,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13028,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13028,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13028,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13028,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13028,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13028,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13028,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13028,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13028,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13028,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13028,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13028,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13028,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13028,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13028,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13028,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13028,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13028,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13028,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13028,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13028,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13028,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13028 : FrameRepair 13028 scalarRow13028 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13028Cells j).1 (repair13028Cells j).2.1
  endpoint_upper := fun j => ((repair13028Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13028Cells j).2.2

theorem repair13029Cells (j : Fin 43) :
    0 ≤ (scalarRow13029.table (sourceIndex j)).upper ∧
    (scalarRow13029.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13029.table (sourceIndex j)).centre) /
      (scalarRow13029.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13029.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13029,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13029,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13029,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13029,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13029,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13029,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13029,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13029,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13029,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13029,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13029,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13029,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13029,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13029,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13029,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13029,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13029,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13029,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13029,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13029,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13029,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13029,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13029,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13029,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13029,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13029,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13029,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13029,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13029,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13029,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13029,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13029,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13029,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13029,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13029,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13029,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13029,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13029,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13029,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13029,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13029,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13029,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13029,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13029,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13029,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13029,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13029,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13029,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13029,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13029,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13029,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13029,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13029,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13029,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13029,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13029,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13029,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13029,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13029,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13029,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13029,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13029,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13029,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13029,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13029,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13029,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13029,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13029,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13029,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13029,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13029,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13029,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13029,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13029,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13029,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13029,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13029,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13029,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13029,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13029,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13029,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13029,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13029,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13029,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13029,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13029,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13029 : FrameRepair 13029 scalarRow13029 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13029Cells j).1 (repair13029Cells j).2.1
  endpoint_upper := fun j => ((repair13029Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13029Cells j).2.2

theorem repair13030Cells (j : Fin 43) :
    0 ≤ (scalarRow13030.table (sourceIndex j)).upper ∧
    (scalarRow13030.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13030.table (sourceIndex j)).centre) /
      (scalarRow13030.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13030.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13030,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13030,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13030,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13030,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13030,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13030,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13030,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13030,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13030,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13030,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13030,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13030,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13030,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13030,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13030,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13030,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13030,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13030,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13030,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13030,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13030,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13030,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13030,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13030,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13030,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13030,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13030,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13030,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13030,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13030,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13030,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13030,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13030,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13030,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13030,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13030,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13030,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13030,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13030,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13030,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13030,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13030,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13030,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13030,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13030,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13030,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13030,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13030,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13030,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13030,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13030,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13030,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13030,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13030,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13030,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13030,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13030,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13030,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13030,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13030,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13030,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13030,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13030,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13030,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13030,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13030,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13030,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13030,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13030,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13030,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13030,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13030,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13030,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13030,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13030,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13030,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13030,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13030,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13030,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13030,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13030,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13030,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13030,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13030,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13030,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13030,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13030 : FrameRepair 13030 scalarRow13030 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13030Cells j).1 (repair13030Cells j).2.1
  endpoint_upper := fun j => ((repair13030Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13030Cells j).2.2

theorem repair13031Cells (j : Fin 43) :
    0 ≤ (scalarRow13031.table (sourceIndex j)).upper ∧
    (scalarRow13031.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13031.table (sourceIndex j)).centre) /
      (scalarRow13031.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13031.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13031,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13031,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13031,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13031,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13031,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13031,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13031,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13031,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13031,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13031,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13031,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13031,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13031,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13031,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13031,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13031,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13031,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13031,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13031,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13031,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13031,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13031,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13031,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13031,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13031,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13031,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13031,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13031,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13031,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13031,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13031,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13031,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13031,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13031,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13031,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13031,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13031,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13031,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13031,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13031,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13031,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13031,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13031,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13031,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13031,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13031,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13031,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13031,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13031,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13031,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13031,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13031,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13031,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13031,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13031,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13031,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13031,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13031,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13031,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13031,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13031,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13031,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13031,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13031,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13031,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13031,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13031,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13031,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13031,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13031,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13031,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13031,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13031,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13031,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13031,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13031,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13031,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13031,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13031,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13031,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13031,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13031,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13031,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13031,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13031,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13031,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13031 : FrameRepair 13031 scalarRow13031 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13031Cells j).1 (repair13031Cells j).2.1
  endpoint_upper := fun j => ((repair13031Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13031Cells j).2.2

theorem repair13032Cells (j : Fin 43) :
    0 ≤ (scalarRow13032.table (sourceIndex j)).upper ∧
    (scalarRow13032.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13032.table (sourceIndex j)).centre) /
      (scalarRow13032.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13032.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13032,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13032,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13032,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13032,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13032,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13032,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13032,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13032,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13032,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13032,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13032,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13032,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13032,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13032,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13032,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13032,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13032,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13032,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13032,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13032,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13032,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13032,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13032,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13032,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13032,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13032,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13032,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13032,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13032,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13032,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13032,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13032,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13032,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13032,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13032,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13032,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13032,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13032,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13032,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13032,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13032,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13032,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13032,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13032,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13032,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13032,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13032,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13032,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13032,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13032,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13032,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13032,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13032,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13032,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13032,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13032,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13032,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13032,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13032,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13032,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13032,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13032,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13032,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13032,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13032,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13032,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13032,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13032,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13032,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13032,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13032,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13032,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13032,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13032,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13032,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13032,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13032,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13032,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13032,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13032,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13032,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13032,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13032,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13032,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13032,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13032,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13032 : FrameRepair 13032 scalarRow13032 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13032Cells j).1 (repair13032Cells j).2.1
  endpoint_upper := fun j => ((repair13032Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13032Cells j).2.2

theorem repair13033Cells (j : Fin 43) :
    0 ≤ (scalarRow13033.table (sourceIndex j)).upper ∧
    (scalarRow13033.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13033.table (sourceIndex j)).centre) /
      (scalarRow13033.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13033.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13033,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13033,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13033,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13033,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13033,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13033,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13033,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13033,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13033,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13033,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13033,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13033,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13033,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13033,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13033,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13033,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13033,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13033,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13033,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13033,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13033,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13033,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13033,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13033,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13033,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13033,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13033,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13033,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13033,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13033,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13033,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13033,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13033,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13033,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13033,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13033,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13033,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13033,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13033,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13033,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13033,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13033,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13033,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13033,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13033,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13033,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13033,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13033,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13033,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13033,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13033,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13033,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13033,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13033,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13033,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13033,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13033,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13033,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13033,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13033,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13033,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13033,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13033,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13033,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13033,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13033,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13033,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13033,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13033,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13033,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13033,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13033,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13033,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13033,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13033,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13033,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13033,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13033,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13033,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13033,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13033,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13033,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13033,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13033,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13033,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13033,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13033 : FrameRepair 13033 scalarRow13033 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13033Cells j).1 (repair13033Cells j).2.1
  endpoint_upper := fun j => ((repair13033Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13033Cells j).2.2

theorem repair13034Cells (j : Fin 43) :
    0 ≤ (scalarRow13034.table (sourceIndex j)).upper ∧
    (scalarRow13034.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13034.table (sourceIndex j)).centre) /
      (scalarRow13034.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13034.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13034,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13034,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13034,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13034,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13034,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13034,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13034,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13034,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13034,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13034,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13034,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13034,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13034,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13034,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13034,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13034,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13034,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13034,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13034,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13034,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13034,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13034,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13034,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13034,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13034,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13034,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13034,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13034,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13034,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13034,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13034,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13034,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13034,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13034,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13034,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13034,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13034,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13034,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13034,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13034,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13034,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13034,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13034,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13034,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13034,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13034,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13034,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13034,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13034,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13034,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13034,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13034,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13034,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13034,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13034,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13034,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13034,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13034,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13034,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13034,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13034,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13034,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13034,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13034,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13034,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13034,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13034,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13034,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13034,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13034,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13034,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13034,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13034,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13034,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13034,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13034,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13034,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13034,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13034,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13034,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13034,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13034,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13034,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13034,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13034,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13034,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13034 : FrameRepair 13034 scalarRow13034 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13034Cells j).1 (repair13034Cells j).2.1
  endpoint_upper := fun j => ((repair13034Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13034Cells j).2.2

theorem repair13035Cells (j : Fin 43) :
    0 ≤ (scalarRow13035.table (sourceIndex j)).upper ∧
    (scalarRow13035.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13035.table (sourceIndex j)).centre) /
      (scalarRow13035.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13035.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13035,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13035,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13035,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13035,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13035,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13035,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13035,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13035,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13035,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13035,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13035,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13035,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13035,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13035,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13035,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13035,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13035,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13035,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13035,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13035,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13035,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13035,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13035,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13035,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13035,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13035,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13035,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13035,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13035,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13035,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13035,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13035,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13035,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13035,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13035,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13035,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13035,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13035,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13035,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13035,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13035,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13035,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13035,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13035,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13035,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13035,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13035,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13035,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13035,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13035,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13035,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13035,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13035,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13035,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13035,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13035,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13035,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13035,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13035,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13035,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13035,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13035,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13035,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13035,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13035,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13035,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13035,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13035,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13035,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13035,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13035,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13035,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13035,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13035,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13035,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13035,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13035,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13035,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13035,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13035,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13035,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13035,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13035,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13035,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13035,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13035,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13035 : FrameRepair 13035 scalarRow13035 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13035Cells j).1 (repair13035Cells j).2.1
  endpoint_upper := fun j => ((repair13035Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13035Cells j).2.2

theorem repair13036Cells (j : Fin 43) :
    0 ≤ (scalarRow13036.table (sourceIndex j)).upper ∧
    (scalarRow13036.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13036.table (sourceIndex j)).centre) /
      (scalarRow13036.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13036.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13036,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13036,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13036,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13036,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13036,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13036,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13036,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13036,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13036,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13036,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13036,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13036,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13036,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13036,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13036,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13036,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13036,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13036,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13036,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13036,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13036,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13036,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13036,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13036,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13036,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13036,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13036,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13036,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13036,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13036,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13036,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13036,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13036,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13036,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13036,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13036,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13036,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13036,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13036,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13036,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13036,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13036,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13036,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13036,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13036,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13036,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13036,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13036,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13036,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13036,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13036,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13036,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13036,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13036,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13036,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13036,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13036,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13036,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13036,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13036,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13036,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13036,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13036,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13036,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13036,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13036,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13036,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13036,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13036,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13036,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13036,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13036,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13036,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13036,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13036,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13036,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13036,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13036,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13036,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13036,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13036,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13036,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13036,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13036,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13036,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13036,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13036 : FrameRepair 13036 scalarRow13036 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13036Cells j).1 (repair13036Cells j).2.1
  endpoint_upper := fun j => ((repair13036Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13036Cells j).2.2

theorem repair13037Cells (j : Fin 43) :
    0 ≤ (scalarRow13037.table (sourceIndex j)).upper ∧
    (scalarRow13037.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13037.table (sourceIndex j)).centre) /
      (scalarRow13037.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13037.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13037,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13037,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13037,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13037,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13037,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13037,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13037,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13037,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13037,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13037,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13037,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13037,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13037,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13037,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13037,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13037,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13037,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13037,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13037,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13037,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13037,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13037,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13037,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13037,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13037,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13037,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13037,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13037,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13037,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13037,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13037,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13037,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13037,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13037,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13037,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13037,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13037,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13037,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13037,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13037,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13037,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13037,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13037,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13037,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13037,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13037,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13037,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13037,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13037,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13037,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13037,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13037,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13037,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13037,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13037,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13037,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13037,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13037,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13037,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13037,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13037,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13037,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13037,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13037,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13037,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13037,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13037,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13037,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13037,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13037,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13037,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13037,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13037,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13037,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13037,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13037,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13037,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13037,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13037,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13037,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13037,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13037,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13037,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13037,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13037,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13037,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13037 : FrameRepair 13037 scalarRow13037 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13037Cells j).1 (repair13037Cells j).2.1
  endpoint_upper := fun j => ((repair13037Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13037Cells j).2.2

theorem repair13038Cells (j : Fin 43) :
    0 ≤ (scalarRow13038.table (sourceIndex j)).upper ∧
    (scalarRow13038.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13038.table (sourceIndex j)).centre) /
      (scalarRow13038.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13038.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13038,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13038,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13038,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13038,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13038,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13038,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13038,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13038,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13038,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13038,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13038,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13038,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13038,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13038,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13038,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13038,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13038,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13038,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13038,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13038,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13038,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13038,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13038,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13038,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13038,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13038,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13038,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13038,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13038,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13038,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13038,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13038,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13038,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13038,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13038,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13038,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13038,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13038,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13038,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13038,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13038,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13038,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13038,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13038,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13038,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13038,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13038,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13038,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13038,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13038,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13038,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13038,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13038,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13038,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13038,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13038,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13038,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13038,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13038,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13038,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13038,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13038,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13038,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13038,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13038,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13038,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13038,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13038,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13038,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13038,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13038,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13038,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13038,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13038,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13038,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13038,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13038,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13038,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13038,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13038,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13038,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13038,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13038,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13038,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13038,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13038,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13038 : FrameRepair 13038 scalarRow13038 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13038Cells j).1 (repair13038Cells j).2.1
  endpoint_upper := fun j => ((repair13038Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13038Cells j).2.2

theorem repair13039Cells (j : Fin 43) :
    0 ≤ (scalarRow13039.table (sourceIndex j)).upper ∧
    (scalarRow13039.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13039.table (sourceIndex j)).centre) /
      (scalarRow13039.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13039.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13039,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13039,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13039,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13039,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13039,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13039,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13039,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13039,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13039,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13039,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13039,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13039,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13039,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13039,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13039,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13039,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13039,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13039,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13039,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13039,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13039,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13039,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13039,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13039,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13039,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13039,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13039,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13039,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13039,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13039,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13039,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13039,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13039,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13039,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13039,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13039,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13039,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13039,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13039,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13039,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13039,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13039,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13039,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13039,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13039,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13039,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13039,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13039,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13039,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13039,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13039,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13039,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13039,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13039,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13039,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13039,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13039,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13039,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13039,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13039,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13039,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13039,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13039,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13039,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13039,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13039,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13039,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13039,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13039,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13039,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13039,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13039,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13039,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13039,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13039,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13039,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13039,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13039,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13039,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13039,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13039,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13039,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13039,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13039,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13039,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13039,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13039 : FrameRepair 13039 scalarRow13039 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13039Cells j).1 (repair13039Cells j).2.1
  endpoint_upper := fun j => ((repair13039Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13039Cells j).2.2

theorem repair13040Cells (j : Fin 43) :
    0 ≤ (scalarRow13040.table (sourceIndex j)).upper ∧
    (scalarRow13040.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13040.table (sourceIndex j)).centre) /
      (scalarRow13040.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13040.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13040,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13040,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13040,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13040,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13040,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13040,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13040,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13040,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13040,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13040,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13040,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13040,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13040,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13040,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13040,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13040,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13040,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13040,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13040,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13040,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13040,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13040,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13040,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13040,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13040,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13040,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13040,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13040,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13040,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13040,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13040,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13040,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13040,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13040,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13040,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13040,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13040,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13040,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13040,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13040,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13040,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13040,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13040,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13040,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13040,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13040,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13040,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13040,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13040,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13040,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13040,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13040,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13040,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13040,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13040,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13040,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13040,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13040,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13040,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13040,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13040,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13040,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13040,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13040,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13040,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13040,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13040,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13040,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13040,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13040,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13040,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13040,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13040,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13040,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13040,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13040,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13040,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13040,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13040,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13040,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13040,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13040,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13040,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13040,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13040,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13040,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13040 : FrameRepair 13040 scalarRow13040 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13040Cells j).1 (repair13040Cells j).2.1
  endpoint_upper := fun j => ((repair13040Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13040Cells j).2.2

theorem repair13041Cells (j : Fin 43) :
    0 ≤ (scalarRow13041.table (sourceIndex j)).upper ∧
    (scalarRow13041.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13041.table (sourceIndex j)).centre) /
      (scalarRow13041.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13041.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13041,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13041,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13041,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13041,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13041,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13041,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13041,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13041,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13041,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13041,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13041,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13041,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13041,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13041,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13041,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13041,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13041,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13041,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13041,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13041,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13041,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13041,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13041,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13041,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13041,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13041,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13041,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13041,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13041,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13041,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13041,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13041,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13041,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13041,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13041,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13041,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13041,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13041,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13041,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13041,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13041,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13041,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13041,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13041,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13041,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13041,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13041,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13041,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13041,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13041,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13041,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13041,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13041,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13041,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13041,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13041,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13041,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13041,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13041,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13041,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13041,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13041,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13041,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13041,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13041,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13041,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13041,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13041,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13041,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13041,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13041,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13041,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13041,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13041,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13041,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13041,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13041,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13041,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13041,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13041,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13041,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13041,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13041,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13041,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13041,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13041,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13041 : FrameRepair 13041 scalarRow13041 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13041Cells j).1 (repair13041Cells j).2.1
  endpoint_upper := fun j => ((repair13041Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13041Cells j).2.2

theorem repair13042Cells (j : Fin 43) :
    0 ≤ (scalarRow13042.table (sourceIndex j)).upper ∧
    (scalarRow13042.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13042.table (sourceIndex j)).centre) /
      (scalarRow13042.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13042.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13042,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13042,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13042,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13042,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13042,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13042,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13042,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13042,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13042,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13042,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13042,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13042,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13042,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13042,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13042,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13042,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13042,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13042,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13042,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13042,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13042,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13042,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13042,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13042,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13042,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13042,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13042,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13042,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13042,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13042,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13042,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13042,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13042,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13042,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13042,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13042,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13042,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13042,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13042,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13042,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13042,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13042,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13042,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13042,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13042,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13042,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13042,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13042,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13042,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13042,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13042,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13042,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13042,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13042,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13042,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13042,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13042,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13042,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13042,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13042,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13042,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13042,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13042,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13042,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13042,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13042,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13042,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13042,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13042,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13042,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13042,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13042,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13042,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13042,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13042,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13042,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13042,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13042,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13042,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13042,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13042,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13042,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13042,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13042,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13042,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13042,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13042 : FrameRepair 13042 scalarRow13042 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13042Cells j).1 (repair13042Cells j).2.1
  endpoint_upper := fun j => ((repair13042Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13042Cells j).2.2

theorem repair13043Cells (j : Fin 43) :
    0 ≤ (scalarRow13043.table (sourceIndex j)).upper ∧
    (scalarRow13043.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13043.table (sourceIndex j)).centre) /
      (scalarRow13043.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13043.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13043,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13043,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13043,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13043,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13043,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13043,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13043,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13043,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13043,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13043,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13043,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13043,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13043,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13043,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13043,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13043,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13043,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13043,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13043,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13043,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13043,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13043,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13043,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13043,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13043,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13043,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13043,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13043,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13043,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13043,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13043,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13043,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13043,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13043,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13043,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13043,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13043,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13043,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13043,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13043,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13043,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13043,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13043,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13043,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13043,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13043,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13043,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13043,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13043,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13043,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13043,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13043,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13043,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13043,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13043,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13043,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13043,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13043,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13043,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13043,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13043,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13043,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13043,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13043,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13043,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13043,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13043,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13043,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13043,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13043,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13043,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13043,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13043,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13043,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13043,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13043,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13043,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13043,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13043,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13043,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13043,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13043,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13043,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13043,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13043,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13043,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13043 : FrameRepair 13043 scalarRow13043 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13043Cells j).1 (repair13043Cells j).2.1
  endpoint_upper := fun j => ((repair13043Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13043Cells j).2.2

theorem repair13044Cells (j : Fin 43) :
    0 ≤ (scalarRow13044.table (sourceIndex j)).upper ∧
    (scalarRow13044.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13044.table (sourceIndex j)).centre) /
      (scalarRow13044.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13044.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13044,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13044,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13044,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13044,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13044,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13044,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13044,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13044,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13044,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13044,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13044,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13044,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13044,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13044,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13044,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13044,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13044,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13044,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13044,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13044,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13044,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13044,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13044,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13044,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13044,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13044,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13044,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13044,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13044,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13044,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13044,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13044,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13044,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13044,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13044,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13044,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13044,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13044,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13044,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13044,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13044,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13044,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13044,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13044,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13044,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13044,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13044,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13044,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13044,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13044,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13044,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13044,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13044,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13044,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13044,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13044,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13044,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13044,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13044,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13044,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13044,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13044,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13044,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13044,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13044,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13044,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13044,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13044,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13044,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13044,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13044,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13044,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13044,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13044,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13044,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13044,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13044,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13044,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13044,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13044,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13044,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13044,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13044,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13044,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13044,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13044,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13044 : FrameRepair 13044 scalarRow13044 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13044Cells j).1 (repair13044Cells j).2.1
  endpoint_upper := fun j => ((repair13044Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13044Cells j).2.2

theorem repair13045Cells (j : Fin 43) :
    0 ≤ (scalarRow13045.table (sourceIndex j)).upper ∧
    (scalarRow13045.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13045.table (sourceIndex j)).centre) /
      (scalarRow13045.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13045.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13045,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13045,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13045,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13045,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13045,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13045,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13045,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13045,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13045,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13045,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13045,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13045,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13045,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13045,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13045,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13045,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13045,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13045,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13045,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13045,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13045,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13045,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13045,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13045,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13045,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13045,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13045,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13045,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13045,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13045,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13045,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13045,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13045,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13045,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13045,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13045,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13045,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13045,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13045,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13045,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13045,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13045,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13045,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13045,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13045,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13045,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13045,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13045,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13045,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13045,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13045,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13045,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13045,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13045,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13045,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13045,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13045,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13045,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13045,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13045,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13045,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13045,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13045,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13045,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13045,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13045,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13045,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13045,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13045,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13045,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13045,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13045,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13045,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13045,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13045,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13045,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13045,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13045,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13045,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13045,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13045,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13045,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13045,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13045,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13045,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13045,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13045 : FrameRepair 13045 scalarRow13045 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13045Cells j).1 (repair13045Cells j).2.1
  endpoint_upper := fun j => ((repair13045Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13045Cells j).2.2

theorem repair13046Cells (j : Fin 43) :
    0 ≤ (scalarRow13046.table (sourceIndex j)).upper ∧
    (scalarRow13046.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13046.table (sourceIndex j)).centre) /
      (scalarRow13046.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13046.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13046,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13046,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13046,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13046,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13046,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13046,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13046,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13046,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13046,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13046,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13046,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13046,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13046,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13046,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13046,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13046,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13046,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13046,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13046,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13046,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13046,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13046,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13046,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13046,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13046,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13046,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13046,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13046,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13046,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13046,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13046,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13046,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13046,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13046,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13046,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13046,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13046,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13046,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13046,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13046,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13046,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13046,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13046,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13046,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13046,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13046,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13046,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13046,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13046,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13046,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13046,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13046,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13046,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13046,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13046,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13046,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13046,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13046,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13046,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13046,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13046,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13046,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13046,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13046,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13046,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13046,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13046,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13046,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13046,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13046,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13046,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13046,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13046,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13046,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13046,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13046,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13046,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13046,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13046,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13046,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13046,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13046,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13046,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13046,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13046,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13046,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13046 : FrameRepair 13046 scalarRow13046 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13046Cells j).1 (repair13046Cells j).2.1
  endpoint_upper := fun j => ((repair13046Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13046Cells j).2.2

theorem repair13047Cells (j : Fin 43) :
    0 ≤ (scalarRow13047.table (sourceIndex j)).upper ∧
    (scalarRow13047.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13047.table (sourceIndex j)).centre) /
      (scalarRow13047.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13047.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13047,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13047,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13047,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13047,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13047,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13047,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13047,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13047,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13047,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13047,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13047,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13047,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13047,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13047,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13047,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13047,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13047,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13047,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13047,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13047,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13047,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13047,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13047,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13047,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13047,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13047,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13047,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13047,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13047,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13047,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13047,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13047,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13047,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13047,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13047,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13047,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13047,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13047,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13047,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13047,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13047,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13047,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13047,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13047,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13047,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13047,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13047,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13047,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13047,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13047,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13047,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13047,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13047,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13047,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13047,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13047,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13047,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13047,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13047,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13047,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13047,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13047,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13047,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13047,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13047,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13047,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13047,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13047,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13047,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13047,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13047,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13047,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13047,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13047,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13047,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13047,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13047,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13047,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13047,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13047,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13047,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13047,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13047,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13047,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13047,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13047,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13047 : FrameRepair 13047 scalarRow13047 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13047Cells j).1 (repair13047Cells j).2.1
  endpoint_upper := fun j => ((repair13047Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13047Cells j).2.2

theorem repair13048Cells (j : Fin 43) :
    0 ≤ (scalarRow13048.table (sourceIndex j)).upper ∧
    (scalarRow13048.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13048.table (sourceIndex j)).centre) /
      (scalarRow13048.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13048.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13048,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13048,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13048,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13048,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13048,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13048,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13048,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13048,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13048,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13048,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13048,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13048,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13048,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13048,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13048,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13048,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13048,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13048,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13048,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13048,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13048,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13048,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13048,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13048,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13048,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13048,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13048,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13048,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13048,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13048,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13048,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13048,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13048,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13048,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13048,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13048,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13048,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13048,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13048,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13048,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13048,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13048,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13048,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13048,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13048,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13048,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13048,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13048,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13048,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13048,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13048,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13048,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13048,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13048,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13048,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13048,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13048,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13048,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13048,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13048,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13048,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13048,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13048,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13048,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13048,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13048,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13048,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13048,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13048,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13048,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13048,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13048,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13048,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13048,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13048,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13048,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13048,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13048,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13048,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13048,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13048,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13048,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13048,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13048,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13048,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13048,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13048 : FrameRepair 13048 scalarRow13048 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13048Cells j).1 (repair13048Cells j).2.1
  endpoint_upper := fun j => ((repair13048Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13048Cells j).2.2

theorem repair13049Cells (j : Fin 43) :
    0 ≤ (scalarRow13049.table (sourceIndex j)).upper ∧
    (scalarRow13049.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13049.table (sourceIndex j)).centre) /
      (scalarRow13049.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13049.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13049,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13049,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13049,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13049,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13049,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13049,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13049,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13049,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13049,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13049,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13049,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13049,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13049,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13049,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13049,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13049,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13049,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13049,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13049,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13049,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13049,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13049,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13049,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13049,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13049,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13049,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13049,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13049,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13049,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13049,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13049,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13049,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13049,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13049,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13049,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13049,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13049,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13049,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13049,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13049,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13049,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13049,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13049,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13049,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13049,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13049,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13049,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13049,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13049,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13049,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13049,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13049,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13049,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13049,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13049,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13049,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13049,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13049,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13049,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13049,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13049,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13049,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13049,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13049,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13049,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13049,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13049,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13049,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13049,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13049,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13049,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13049,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13049,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13049,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13049,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13049,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13049,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13049,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13049,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13049,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13049,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13049,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13049,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13049,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13049,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13049,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13049 : FrameRepair 13049 scalarRow13049 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13049Cells j).1 (repair13049Cells j).2.1
  endpoint_upper := fun j => ((repair13049Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13049Cells j).2.2

end BstLean.Part269
