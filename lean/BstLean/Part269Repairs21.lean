import BstLean.Part269Rows21
import BstLean.Part269RepairCommon
namespace BstLean.Part269
open Real Set BstLean.Part255 BstLean.Part263 BstLean.Part264
theorem repair12875Cells (j : Fin 43) :
    0 ≤ (scalarRow12875.table (sourceIndex j)).upper ∧
    (scalarRow12875.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12875.table (sourceIndex j)).centre) /
      (scalarRow12875.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12875.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12875,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12875,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12875,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12875,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12875,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12875,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12875,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12875,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12875,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12875,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12875,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12875,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12875,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12875,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12875,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12875,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12875,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12875,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12875,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12875,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12875,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12875,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12875,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12875,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12875,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12875,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12875,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12875,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12875,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12875,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12875,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12875,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12875,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12875,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12875,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12875,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12875,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12875,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12875,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12875,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12875,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12875,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12875,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12875,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12875,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12875,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12875,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12875,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12875,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12875,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12875,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12875,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12875,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12875,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12875,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12875,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12875,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12875,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12875,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12875,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12875,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12875,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12875,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12875,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12875,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12875,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12875,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12875,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12875,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12875,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12875,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12875,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12875,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12875,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12875,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12875,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12875,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12875,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12875,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12875,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12875,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12875,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12875,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12875,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12875,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12875,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12875 : FrameRepair 12875 scalarRow12875 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12875Cells j).1 (repair12875Cells j).2.1
  endpoint_upper := fun j => ((repair12875Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12875Cells j).2.2

theorem repair12876Cells (j : Fin 43) :
    0 ≤ (scalarRow12876.table (sourceIndex j)).upper ∧
    (scalarRow12876.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12876.table (sourceIndex j)).centre) /
      (scalarRow12876.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12876.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12876,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12876,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12876,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12876,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12876,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12876,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12876,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12876,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12876,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12876,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12876,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12876,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12876,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12876,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12876,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12876,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12876,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12876,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12876,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12876,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12876,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12876,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12876,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12876,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12876,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12876,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12876,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12876,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12876,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12876,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12876,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12876,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12876,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12876,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12876,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12876,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12876,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12876,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12876,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12876,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12876,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12876,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12876,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12876,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12876,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12876,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12876,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12876,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12876,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12876,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12876,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12876,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12876,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12876,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12876,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12876,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12876,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12876,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12876,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12876,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12876,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12876,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12876,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12876,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12876,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12876,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12876,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12876,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12876,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12876,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12876,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12876,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12876,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12876,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12876,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12876,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12876,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12876,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12876,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12876,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12876,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12876,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12876,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12876,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12876,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12876,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12876 : FrameRepair 12876 scalarRow12876 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12876Cells j).1 (repair12876Cells j).2.1
  endpoint_upper := fun j => ((repair12876Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12876Cells j).2.2

theorem repair12877Cells (j : Fin 43) :
    0 ≤ (scalarRow12877.table (sourceIndex j)).upper ∧
    (scalarRow12877.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12877.table (sourceIndex j)).centre) /
      (scalarRow12877.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12877.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12877,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12877,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12877,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12877,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12877,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12877,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12877,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12877,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12877,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12877,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12877,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12877,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12877,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12877,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12877,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12877,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12877,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12877,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12877,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12877,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12877,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12877,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12877,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12877,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12877,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12877,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12877,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12877,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12877,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12877,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12877,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12877,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12877,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12877,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12877,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12877,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12877,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12877,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12877,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12877,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12877,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12877,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12877,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12877,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12877,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12877,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12877,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12877,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12877,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12877,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12877,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12877,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12877,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12877,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12877,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12877,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12877,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12877,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12877,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12877,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12877,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12877,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12877,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12877,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12877,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12877,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12877,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12877,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12877,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12877,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12877,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12877,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12877,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12877,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12877,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12877,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12877,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12877,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12877,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12877,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12877,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12877,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12877,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12877,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12877,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12877,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12877 : FrameRepair 12877 scalarRow12877 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12877Cells j).1 (repair12877Cells j).2.1
  endpoint_upper := fun j => ((repair12877Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12877Cells j).2.2

theorem repair12878Cells (j : Fin 43) :
    0 ≤ (scalarRow12878.table (sourceIndex j)).upper ∧
    (scalarRow12878.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12878.table (sourceIndex j)).centre) /
      (scalarRow12878.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12878.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12878,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12878,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12878,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12878,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12878,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12878,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12878,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12878,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12878,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12878,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12878,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12878,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12878,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12878,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12878,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12878,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12878,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12878,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12878,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12878,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12878,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12878,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12878,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12878,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12878,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12878,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12878,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12878,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12878,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12878,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12878,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12878,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12878,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12878,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12878,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12878,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12878,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12878,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12878,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12878,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12878,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12878,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12878,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12878,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12878,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12878,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12878,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12878,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12878,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12878,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12878,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12878,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12878,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12878,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12878,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12878,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12878,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12878,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12878,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12878,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12878,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12878,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12878,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12878,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12878,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12878,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12878,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12878,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12878,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12878,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12878,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12878,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12878,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12878,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12878,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12878,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12878,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12878,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12878,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12878,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12878,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12878,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12878,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12878,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12878,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12878,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12878 : FrameRepair 12878 scalarRow12878 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12878Cells j).1 (repair12878Cells j).2.1
  endpoint_upper := fun j => ((repair12878Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12878Cells j).2.2

theorem repair12879Cells (j : Fin 43) :
    0 ≤ (scalarRow12879.table (sourceIndex j)).upper ∧
    (scalarRow12879.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12879.table (sourceIndex j)).centre) /
      (scalarRow12879.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12879.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12879,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12879,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12879,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12879,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12879,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12879,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12879,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12879,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12879,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12879,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12879,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12879,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12879,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12879,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12879,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12879,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12879,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12879,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12879,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12879,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12879,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12879,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12879,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12879,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12879,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12879,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12879,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12879,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12879,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12879,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12879,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12879,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12879,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12879,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12879,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12879,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12879,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12879,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12879,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12879,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12879,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12879,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12879,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12879,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12879,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12879,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12879,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12879,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12879,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12879,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12879,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12879,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12879,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12879,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12879,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12879,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12879,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12879,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12879,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12879,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12879,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12879,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12879,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12879,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12879,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12879,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12879,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12879,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12879,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12879,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12879,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12879,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12879,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12879,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12879,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12879,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12879,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12879,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12879,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12879,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12879,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12879,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12879,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12879,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12879,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12879,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12879 : FrameRepair 12879 scalarRow12879 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12879Cells j).1 (repair12879Cells j).2.1
  endpoint_upper := fun j => ((repair12879Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12879Cells j).2.2

theorem repair12880Cells (j : Fin 43) :
    0 ≤ (scalarRow12880.table (sourceIndex j)).upper ∧
    (scalarRow12880.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12880.table (sourceIndex j)).centre) /
      (scalarRow12880.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12880.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12880,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12880,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12880,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12880,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12880,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12880,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12880,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12880,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12880,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12880,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12880,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12880,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12880,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12880,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12880,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12880,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12880,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12880,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12880,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12880,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12880,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12880,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12880,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12880,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12880,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12880,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12880,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12880,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12880,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12880,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12880,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12880,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12880,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12880,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12880,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12880,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12880,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12880,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12880,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12880,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12880,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12880,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12880,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12880,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12880,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12880,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12880,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12880,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12880,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12880,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12880,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12880,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12880,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12880,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12880,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12880,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12880,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12880,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12880,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12880,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12880,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12880,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12880,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12880,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12880,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12880,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12880,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12880,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12880,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12880,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12880,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12880,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12880,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12880,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12880,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12880,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12880,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12880,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12880,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12880,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12880,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12880,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12880,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12880,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12880,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12880,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12880 : FrameRepair 12880 scalarRow12880 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12880Cells j).1 (repair12880Cells j).2.1
  endpoint_upper := fun j => ((repair12880Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12880Cells j).2.2

theorem repair12881Cells (j : Fin 43) :
    0 ≤ (scalarRow12881.table (sourceIndex j)).upper ∧
    (scalarRow12881.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12881.table (sourceIndex j)).centre) /
      (scalarRow12881.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12881.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12881,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12881,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12881,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12881,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12881,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12881,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12881,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12881,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12881,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12881,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12881,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12881,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12881,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12881,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12881,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12881,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12881,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12881,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12881,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12881,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12881,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12881,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12881,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12881,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12881,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12881,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12881,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12881,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12881,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12881,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12881,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12881,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12881,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12881,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12881,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12881,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12881,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12881,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12881,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12881,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12881,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12881,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12881,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12881,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12881,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12881,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12881,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12881,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12881,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12881,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12881,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12881,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12881,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12881,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12881,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12881,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12881,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12881,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12881,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12881,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12881,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12881,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12881,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12881,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12881,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12881,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12881,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12881,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12881,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12881,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12881,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12881,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12881,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12881,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12881,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12881,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12881,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12881,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12881,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12881,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12881,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12881,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12881,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12881,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12881,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12881,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12881 : FrameRepair 12881 scalarRow12881 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12881Cells j).1 (repair12881Cells j).2.1
  endpoint_upper := fun j => ((repair12881Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12881Cells j).2.2

theorem repair12882Cells (j : Fin 43) :
    0 ≤ (scalarRow12882.table (sourceIndex j)).upper ∧
    (scalarRow12882.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12882.table (sourceIndex j)).centre) /
      (scalarRow12882.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12882.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12882,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12882,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12882,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12882,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12882,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12882,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12882,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12882,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12882,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12882,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12882,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12882,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12882,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12882,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12882,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12882,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12882,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12882,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12882,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12882,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12882,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12882,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12882,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12882,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12882,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12882,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12882,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12882,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12882,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12882,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12882,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12882,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12882,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12882,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12882,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12882,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12882,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12882,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12882,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12882,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12882,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12882,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12882,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12882,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12882,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12882,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12882,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12882,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12882,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12882,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12882,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12882,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12882,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12882,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12882,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12882,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12882,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12882,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12882,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12882,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12882,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12882,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12882,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12882,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12882,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12882,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12882,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12882,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12882,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12882,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12882,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12882,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12882,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12882,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12882,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12882,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12882,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12882,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12882,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12882,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12882,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12882,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12882,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12882,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12882,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12882,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12882 : FrameRepair 12882 scalarRow12882 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12882Cells j).1 (repair12882Cells j).2.1
  endpoint_upper := fun j => ((repair12882Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12882Cells j).2.2

theorem repair12883Cells (j : Fin 43) :
    0 ≤ (scalarRow12883.table (sourceIndex j)).upper ∧
    (scalarRow12883.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12883.table (sourceIndex j)).centre) /
      (scalarRow12883.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12883.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12883,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12883,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12883,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12883,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12883,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12883,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12883,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12883,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12883,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12883,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12883,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12883,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12883,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12883,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12883,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12883,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12883,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12883,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12883,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12883,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12883,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12883,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12883,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12883,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12883,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12883,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12883,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12883,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12883,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12883,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12883,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12883,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12883,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12883,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12883,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12883,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12883,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12883,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12883,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12883,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12883,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12883,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12883,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12883,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12883,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12883,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12883,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12883,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12883,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12883,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12883,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12883,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12883,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12883,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12883,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12883,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12883,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12883,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12883,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12883,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12883,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12883,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12883,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12883,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12883,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12883,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12883,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12883,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12883,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12883,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12883,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12883,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12883,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12883,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12883,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12883,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12883,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12883,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12883,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12883,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12883,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12883,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12883,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12883,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12883,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12883,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12883 : FrameRepair 12883 scalarRow12883 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12883Cells j).1 (repair12883Cells j).2.1
  endpoint_upper := fun j => ((repair12883Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12883Cells j).2.2

theorem repair12884Cells (j : Fin 43) :
    0 ≤ (scalarRow12884.table (sourceIndex j)).upper ∧
    (scalarRow12884.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12884.table (sourceIndex j)).centre) /
      (scalarRow12884.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12884.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12884,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12884,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12884,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12884,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12884,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12884,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12884,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12884,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12884,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12884,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12884,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12884,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12884,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12884,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12884,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12884,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12884,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12884,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12884,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12884,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12884,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12884,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12884,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12884,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12884,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12884,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12884,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12884,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12884,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12884,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12884,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12884,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12884,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12884,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12884,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12884,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12884,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12884,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12884,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12884,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12884,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12884,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12884,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12884,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12884,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12884,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12884,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12884,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12884,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12884,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12884,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12884,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12884,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12884,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12884,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12884,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12884,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12884,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12884,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12884,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12884,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12884,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12884,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12884,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12884,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12884,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12884,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12884,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12884,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12884,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12884,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12884,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12884,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12884,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12884,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12884,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12884,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12884,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12884,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12884,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12884,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12884,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12884,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12884,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12884,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12884,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12884 : FrameRepair 12884 scalarRow12884 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12884Cells j).1 (repair12884Cells j).2.1
  endpoint_upper := fun j => ((repair12884Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12884Cells j).2.2

theorem repair12885Cells (j : Fin 43) :
    0 ≤ (scalarRow12885.table (sourceIndex j)).upper ∧
    (scalarRow12885.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12885.table (sourceIndex j)).centre) /
      (scalarRow12885.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12885.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12885,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12885,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12885,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12885,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12885,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12885,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12885,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12885,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12885,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12885,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12885,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12885,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12885,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12885,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12885,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12885,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12885,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12885,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12885,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12885,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12885,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12885,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12885,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12885,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12885,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12885,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12885,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12885,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12885,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12885,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12885,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12885,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12885,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12885,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12885,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12885,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12885,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12885,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12885,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12885,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12885,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12885,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12885,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12885,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12885,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12885,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12885,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12885,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12885,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12885,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12885,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12885,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12885,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12885,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12885,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12885,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12885,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12885,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12885,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12885,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12885,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12885,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12885,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12885,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12885,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12885,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12885,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12885,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12885,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12885,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12885,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12885,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12885,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12885,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12885,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12885,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12885,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12885,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12885,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12885,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12885,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12885,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12885,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12885,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12885,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12885,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12885 : FrameRepair 12885 scalarRow12885 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12885Cells j).1 (repair12885Cells j).2.1
  endpoint_upper := fun j => ((repair12885Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12885Cells j).2.2

theorem repair12886Cells (j : Fin 43) :
    0 ≤ (scalarRow12886.table (sourceIndex j)).upper ∧
    (scalarRow12886.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12886.table (sourceIndex j)).centre) /
      (scalarRow12886.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12886.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12886,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12886,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12886,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12886,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12886,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12886,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12886,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12886,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12886,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12886,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12886,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12886,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12886,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12886,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12886,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12886,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12886,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12886,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12886,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12886,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12886,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12886,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12886,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12886,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12886,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12886,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12886,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12886,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12886,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12886,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12886,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12886,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12886,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12886,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12886,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12886,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12886,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12886,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12886,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12886,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12886,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12886,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12886,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12886,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12886,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12886,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12886,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12886,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12886,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12886,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12886,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12886,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12886,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12886,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12886,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12886,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12886,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12886,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12886,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12886,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12886,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12886,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12886,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12886,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12886,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12886,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12886,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12886,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12886,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12886,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12886,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12886,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12886,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12886,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12886,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12886,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12886,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12886,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12886,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12886,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12886,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12886,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12886,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12886,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12886,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12886,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12886 : FrameRepair 12886 scalarRow12886 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12886Cells j).1 (repair12886Cells j).2.1
  endpoint_upper := fun j => ((repair12886Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12886Cells j).2.2

theorem repair12887Cells (j : Fin 43) :
    0 ≤ (scalarRow12887.table (sourceIndex j)).upper ∧
    (scalarRow12887.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12887.table (sourceIndex j)).centre) /
      (scalarRow12887.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12887.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12887,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12887,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12887,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12887,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12887,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12887,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12887,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12887,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12887,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12887,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12887,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12887,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12887,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12887,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12887,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12887,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12887,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12887,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12887,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12887,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12887,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12887,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12887,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12887,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12887,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12887,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12887,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12887,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12887,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12887,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12887,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12887,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12887,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12887,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12887,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12887,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12887,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12887,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12887,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12887,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12887,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12887,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12887,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12887,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12887,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12887,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12887,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12887,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12887,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12887,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12887,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12887,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12887,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12887,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12887,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12887,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12887,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12887,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12887,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12887,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12887,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12887,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12887,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12887,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12887,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12887,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12887,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12887,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12887,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12887,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12887,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12887,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12887,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12887,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12887,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12887,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12887,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12887,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12887,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12887,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12887,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12887,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12887,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12887,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12887,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12887,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12887 : FrameRepair 12887 scalarRow12887 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12887Cells j).1 (repair12887Cells j).2.1
  endpoint_upper := fun j => ((repair12887Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12887Cells j).2.2

theorem repair12888Cells (j : Fin 43) :
    0 ≤ (scalarRow12888.table (sourceIndex j)).upper ∧
    (scalarRow12888.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12888.table (sourceIndex j)).centre) /
      (scalarRow12888.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12888.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12888,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12888,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12888,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12888,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12888,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12888,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12888,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12888,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12888,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12888,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12888,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12888,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12888,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12888,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12888,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12888,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12888,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12888,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12888,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12888,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12888,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12888,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12888,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12888,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12888,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12888,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12888,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12888,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12888,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12888,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12888,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12888,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12888,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12888,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12888,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12888,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12888,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12888,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12888,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12888,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12888,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12888,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12888,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12888,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12888,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12888,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12888,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12888,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12888,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12888,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12888,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12888,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12888,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12888,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12888,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12888,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12888,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12888,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12888,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12888,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12888,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12888,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12888,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12888,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12888,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12888,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12888,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12888,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12888,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12888,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12888,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12888,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12888,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12888,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12888,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12888,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12888,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12888,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12888,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12888,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12888,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12888,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12888,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12888,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12888,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12888,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12888 : FrameRepair 12888 scalarRow12888 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12888Cells j).1 (repair12888Cells j).2.1
  endpoint_upper := fun j => ((repair12888Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12888Cells j).2.2

theorem repair12889Cells (j : Fin 43) :
    0 ≤ (scalarRow12889.table (sourceIndex j)).upper ∧
    (scalarRow12889.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12889.table (sourceIndex j)).centre) /
      (scalarRow12889.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12889.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12889,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12889,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12889,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12889,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12889,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12889,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12889,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12889,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12889,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12889,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12889,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12889,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12889,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12889,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12889,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12889,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12889,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12889,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12889,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12889,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12889,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12889,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12889,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12889,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12889,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12889,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12889,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12889,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12889,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12889,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12889,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12889,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12889,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12889,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12889,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12889,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12889,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12889,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12889,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12889,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12889,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12889,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12889,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12889,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12889,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12889,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12889,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12889,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12889,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12889,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12889,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12889,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12889,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12889,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12889,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12889,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12889,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12889,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12889,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12889,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12889,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12889,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12889,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12889,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12889,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12889,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12889,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12889,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12889,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12889,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12889,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12889,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12889,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12889,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12889,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12889,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12889,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12889,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12889,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12889,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12889,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12889,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12889,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12889,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12889,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12889,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12889 : FrameRepair 12889 scalarRow12889 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12889Cells j).1 (repair12889Cells j).2.1
  endpoint_upper := fun j => ((repair12889Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12889Cells j).2.2

theorem repair12890Cells (j : Fin 43) :
    0 ≤ (scalarRow12890.table (sourceIndex j)).upper ∧
    (scalarRow12890.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12890.table (sourceIndex j)).centre) /
      (scalarRow12890.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12890.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12890,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12890,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12890,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12890,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12890,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12890,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12890,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12890,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12890,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12890,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12890,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12890,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12890,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12890,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12890,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12890,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12890,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12890,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12890,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12890,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12890,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12890,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12890,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12890,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12890,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12890,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12890,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12890,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12890,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12890,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12890,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12890,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12890,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12890,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12890,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12890,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12890,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12890,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12890,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12890,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12890,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12890,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12890,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12890,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12890,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12890,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12890,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12890,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12890,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12890,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12890,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12890,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12890,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12890,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12890,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12890,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12890,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12890,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12890,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12890,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12890,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12890,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12890,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12890,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12890,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12890,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12890,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12890,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12890,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12890,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12890,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12890,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12890,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12890,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12890,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12890,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12890,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12890,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12890,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12890,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12890,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12890,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12890,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12890,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12890,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12890,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12890 : FrameRepair 12890 scalarRow12890 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12890Cells j).1 (repair12890Cells j).2.1
  endpoint_upper := fun j => ((repair12890Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12890Cells j).2.2

theorem repair12891Cells (j : Fin 43) :
    0 ≤ (scalarRow12891.table (sourceIndex j)).upper ∧
    (scalarRow12891.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12891.table (sourceIndex j)).centre) /
      (scalarRow12891.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12891.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12891,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12891,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12891,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12891,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12891,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12891,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12891,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12891,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12891,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12891,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12891,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12891,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12891,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12891,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12891,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12891,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12891,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12891,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12891,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12891,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12891,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12891,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12891,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12891,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12891,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12891,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12891,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12891,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12891,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12891,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12891,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12891,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12891,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12891,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12891,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12891,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12891,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12891,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12891,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12891,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12891,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12891,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12891,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12891,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12891,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12891,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12891,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12891,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12891,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12891,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12891,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12891,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12891,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12891,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12891,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12891,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12891,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12891,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12891,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12891,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12891,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12891,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12891,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12891,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12891,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12891,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12891,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12891,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12891,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12891,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12891,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12891,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12891,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12891,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12891,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12891,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12891,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12891,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12891,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12891,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12891,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12891,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12891,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12891,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12891,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12891,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12891 : FrameRepair 12891 scalarRow12891 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12891Cells j).1 (repair12891Cells j).2.1
  endpoint_upper := fun j => ((repair12891Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12891Cells j).2.2

theorem repair12892Cells (j : Fin 43) :
    0 ≤ (scalarRow12892.table (sourceIndex j)).upper ∧
    (scalarRow12892.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12892.table (sourceIndex j)).centre) /
      (scalarRow12892.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12892.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12892,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12892,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12892,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12892,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12892,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12892,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12892,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12892,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12892,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12892,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12892,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12892,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12892,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12892,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12892,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12892,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12892,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12892,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12892,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12892,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12892,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12892,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12892,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12892,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12892,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12892,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12892,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12892,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12892,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12892,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12892,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12892,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12892,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12892,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12892,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12892,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12892,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12892,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12892,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12892,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12892,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12892,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12892,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12892,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12892,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12892,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12892,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12892,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12892,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12892,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12892,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12892,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12892,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12892,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12892,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12892,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12892,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12892,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12892,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12892,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12892,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12892,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12892,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12892,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12892,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12892,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12892,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12892,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12892,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12892,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12892,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12892,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12892,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12892,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12892,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12892,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12892,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12892,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12892,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12892,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12892,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12892,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12892,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12892,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12892,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12892,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12892 : FrameRepair 12892 scalarRow12892 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12892Cells j).1 (repair12892Cells j).2.1
  endpoint_upper := fun j => ((repair12892Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12892Cells j).2.2

theorem repair12893Cells (j : Fin 43) :
    0 ≤ (scalarRow12893.table (sourceIndex j)).upper ∧
    (scalarRow12893.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12893.table (sourceIndex j)).centre) /
      (scalarRow12893.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12893.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12893,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12893,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12893,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12893,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12893,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12893,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12893,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12893,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12893,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12893,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12893,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12893,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12893,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12893,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12893,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12893,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12893,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12893,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12893,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12893,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12893,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12893,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12893,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12893,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12893,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12893,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12893,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12893,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12893,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12893,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12893,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12893,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12893,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12893,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12893,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12893,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12893,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12893,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12893,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12893,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12893,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12893,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12893,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12893,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12893,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12893,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12893,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12893,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12893,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12893,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12893,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12893,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12893,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12893,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12893,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12893,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12893,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12893,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12893,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12893,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12893,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12893,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12893,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12893,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12893,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12893,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12893,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12893,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12893,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12893,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12893,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12893,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12893,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12893,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12893,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12893,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12893,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12893,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12893,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12893,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12893,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12893,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12893,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12893,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12893,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12893,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12893 : FrameRepair 12893 scalarRow12893 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12893Cells j).1 (repair12893Cells j).2.1
  endpoint_upper := fun j => ((repair12893Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12893Cells j).2.2

theorem repair12894Cells (j : Fin 43) :
    0 ≤ (scalarRow12894.table (sourceIndex j)).upper ∧
    (scalarRow12894.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12894.table (sourceIndex j)).centre) /
      (scalarRow12894.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12894.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12894,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12894,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12894,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12894,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12894,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12894,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12894,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12894,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12894,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12894,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12894,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12894,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12894,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12894,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12894,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12894,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12894,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12894,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12894,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12894,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12894,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12894,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12894,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12894,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12894,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12894,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12894,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12894,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12894,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12894,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12894,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12894,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12894,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12894,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12894,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12894,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12894,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12894,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12894,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12894,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12894,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12894,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12894,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12894,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12894,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12894,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12894,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12894,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12894,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12894,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12894,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12894,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12894,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12894,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12894,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12894,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12894,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12894,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12894,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12894,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12894,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12894,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12894,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12894,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12894,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12894,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12894,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12894,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12894,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12894,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12894,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12894,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12894,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12894,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12894,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12894,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12894,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12894,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12894,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12894,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12894,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12894,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12894,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12894,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12894,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12894,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12894 : FrameRepair 12894 scalarRow12894 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12894Cells j).1 (repair12894Cells j).2.1
  endpoint_upper := fun j => ((repair12894Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12894Cells j).2.2

theorem repair12895Cells (j : Fin 43) :
    0 ≤ (scalarRow12895.table (sourceIndex j)).upper ∧
    (scalarRow12895.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12895.table (sourceIndex j)).centre) /
      (scalarRow12895.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12895.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12895,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12895,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12895,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12895,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12895,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12895,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12895,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12895,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12895,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12895,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12895,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12895,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12895,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12895,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12895,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12895,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12895,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12895,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12895,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12895,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12895,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12895,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12895,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12895,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12895,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12895,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12895,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12895,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12895,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12895,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12895,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12895,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12895,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12895,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12895,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12895,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12895,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12895,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12895,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12895,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12895,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12895,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12895,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12895,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12895,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12895,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12895,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12895,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12895,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12895,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12895,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12895,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12895,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12895,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12895,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12895,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12895,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12895,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12895,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12895,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12895,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12895,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12895,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12895,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12895,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12895,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12895,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12895,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12895,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12895,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12895,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12895,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12895,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12895,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12895,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12895,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12895,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12895,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12895,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12895,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12895,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12895,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12895,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12895,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12895,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12895,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12895 : FrameRepair 12895 scalarRow12895 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12895Cells j).1 (repair12895Cells j).2.1
  endpoint_upper := fun j => ((repair12895Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12895Cells j).2.2

theorem repair12896Cells (j : Fin 43) :
    0 ≤ (scalarRow12896.table (sourceIndex j)).upper ∧
    (scalarRow12896.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12896.table (sourceIndex j)).centre) /
      (scalarRow12896.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12896.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12896,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12896,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12896,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12896,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12896,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12896,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12896,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12896,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12896,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12896,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12896,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12896,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12896,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12896,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12896,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12896,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12896,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12896,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12896,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12896,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12896,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12896,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12896,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12896,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12896,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12896,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12896,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12896,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12896,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12896,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12896,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12896,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12896,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12896,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12896,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12896,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12896,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12896,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12896,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12896,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12896,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12896,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12896,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12896,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12896,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12896,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12896,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12896,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12896,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12896,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12896,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12896,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12896,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12896,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12896,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12896,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12896,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12896,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12896,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12896,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12896,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12896,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12896,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12896,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12896,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12896,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12896,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12896,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12896,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12896,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12896,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12896,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12896,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12896,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12896,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12896,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12896,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12896,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12896,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12896,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12896,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12896,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12896,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12896,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12896,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12896,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12896 : FrameRepair 12896 scalarRow12896 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12896Cells j).1 (repair12896Cells j).2.1
  endpoint_upper := fun j => ((repair12896Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12896Cells j).2.2

theorem repair12897Cells (j : Fin 43) :
    0 ≤ (scalarRow12897.table (sourceIndex j)).upper ∧
    (scalarRow12897.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12897.table (sourceIndex j)).centre) /
      (scalarRow12897.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12897.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12897,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12897,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12897,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12897,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12897,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12897,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12897,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12897,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12897,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12897,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12897,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12897,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12897,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12897,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12897,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12897,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12897,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12897,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12897,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12897,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12897,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12897,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12897,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12897,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12897,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12897,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12897,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12897,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12897,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12897,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12897,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12897,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12897,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12897,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12897,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12897,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12897,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12897,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12897,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12897,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12897,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12897,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12897,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12897,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12897,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12897,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12897,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12897,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12897,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12897,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12897,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12897,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12897,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12897,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12897,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12897,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12897,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12897,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12897,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12897,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12897,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12897,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12897,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12897,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12897,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12897,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12897,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12897,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12897,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12897,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12897,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12897,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12897,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12897,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12897,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12897,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12897,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12897,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12897,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12897,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12897,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12897,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12897,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12897,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12897,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12897,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12897 : FrameRepair 12897 scalarRow12897 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12897Cells j).1 (repair12897Cells j).2.1
  endpoint_upper := fun j => ((repair12897Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12897Cells j).2.2

theorem repair12898Cells (j : Fin 43) :
    0 ≤ (scalarRow12898.table (sourceIndex j)).upper ∧
    (scalarRow12898.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12898.table (sourceIndex j)).centre) /
      (scalarRow12898.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12898.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12898,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12898,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12898,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12898,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12898,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12898,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12898,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12898,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12898,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12898,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12898,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12898,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12898,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12898,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12898,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12898,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12898,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12898,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12898,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12898,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12898,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12898,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12898,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12898,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12898,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12898,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12898,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12898,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12898,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12898,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12898,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12898,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12898,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12898,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12898,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12898,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12898,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12898,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12898,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12898,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12898,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12898,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12898,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12898,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12898,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12898,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12898,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12898,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12898,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12898,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12898,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12898,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12898,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12898,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12898,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12898,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12898,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12898,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12898,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12898,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12898,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12898,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12898,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12898,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12898,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12898,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12898,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12898,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12898,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12898,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12898,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12898,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12898,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12898,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12898,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12898,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12898,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12898,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12898,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12898,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12898,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12898,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12898,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12898,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12898,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12898,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12898 : FrameRepair 12898 scalarRow12898 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12898Cells j).1 (repair12898Cells j).2.1
  endpoint_upper := fun j => ((repair12898Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12898Cells j).2.2

theorem repair12899Cells (j : Fin 43) :
    0 ≤ (scalarRow12899.table (sourceIndex j)).upper ∧
    (scalarRow12899.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12899.table (sourceIndex j)).centre) /
      (scalarRow12899.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12899.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12899,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12899,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12899,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12899,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12899,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12899,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12899,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12899,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12899,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12899,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12899,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12899,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12899,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12899,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12899,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12899,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12899,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12899,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12899,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12899,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12899,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12899,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12899,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12899,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12899,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12899,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12899,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12899,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12899,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12899,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12899,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12899,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12899,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12899,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12899,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12899,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12899,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12899,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12899,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12899,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12899,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12899,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12899,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12899,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12899,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12899,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12899,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12899,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12899,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12899,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12899,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12899,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12899,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12899,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12899,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12899,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12899,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12899,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12899,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12899,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12899,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12899,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12899,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12899,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12899,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12899,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12899,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12899,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12899,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12899,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12899,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12899,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12899,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12899,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12899,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12899,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12899,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12899,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12899,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12899,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12899,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12899,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12899,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12899,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12899,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12899,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12899 : FrameRepair 12899 scalarRow12899 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12899Cells j).1 (repair12899Cells j).2.1
  endpoint_upper := fun j => ((repair12899Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12899Cells j).2.2

end BstLean.Part269
