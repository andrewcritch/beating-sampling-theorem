import BstLean.Part269Rows9
import BstLean.Part269RepairCommon
namespace BstLean.Part269
open Real Set BstLean.Part255 BstLean.Part263 BstLean.Part264
theorem repair12575Cells (j : Fin 43) :
    0 ≤ (scalarRow12575.table (sourceIndex j)).upper ∧
    (scalarRow12575.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12575.table (sourceIndex j)).centre) /
      (scalarRow12575.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12575.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12575,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12575,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12575,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12575,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12575,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12575,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12575,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12575,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12575,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12575,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12575,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12575,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12575,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12575,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12575,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12575,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12575,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12575,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12575,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12575,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12575,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12575,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12575,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12575,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12575,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12575,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12575,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12575,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12575,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12575,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12575,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12575,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12575,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12575,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12575,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12575,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12575,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12575,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12575,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12575,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12575,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12575,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12575,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12575,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12575,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12575,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12575,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12575,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12575,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12575,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12575,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12575,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12575,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12575,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12575,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12575,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12575,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12575,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12575,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12575,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12575,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12575,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12575,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12575,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12575,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12575,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12575,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12575,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12575,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12575,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12575,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12575,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12575,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12575,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12575,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12575,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12575,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12575,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12575,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12575,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12575,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12575,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12575,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12575,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12575,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12575,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12575 : FrameRepair 12575 scalarRow12575 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12575Cells j).1 (repair12575Cells j).2.1
  endpoint_upper := fun j => ((repair12575Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12575Cells j).2.2

theorem repair12576Cells (j : Fin 43) :
    0 ≤ (scalarRow12576.table (sourceIndex j)).upper ∧
    (scalarRow12576.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12576.table (sourceIndex j)).centre) /
      (scalarRow12576.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12576.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12576,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12576,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12576,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12576,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12576,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12576,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12576,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12576,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12576,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12576,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12576,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12576,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12576,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12576,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12576,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12576,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12576,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12576,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12576,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12576,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12576,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12576,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12576,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12576,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12576,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12576,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12576,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12576,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12576,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12576,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12576,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12576,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12576,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12576,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12576,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12576,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12576,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12576,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12576,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12576,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12576,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12576,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12576,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12576,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12576,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12576,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12576,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12576,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12576,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12576,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12576,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12576,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12576,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12576,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12576,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12576,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12576,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12576,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12576,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12576,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12576,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12576,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12576,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12576,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12576,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12576,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12576,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12576,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12576,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12576,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12576,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12576,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12576,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12576,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12576,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12576,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12576,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12576,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12576,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12576,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12576,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12576,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12576,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12576,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12576,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12576,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12576 : FrameRepair 12576 scalarRow12576 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12576Cells j).1 (repair12576Cells j).2.1
  endpoint_upper := fun j => ((repair12576Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12576Cells j).2.2

theorem repair12577Cells (j : Fin 43) :
    0 ≤ (scalarRow12577.table (sourceIndex j)).upper ∧
    (scalarRow12577.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12577.table (sourceIndex j)).centre) /
      (scalarRow12577.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12577.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12577,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12577,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12577,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12577,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12577,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12577,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12577,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12577,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12577,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12577,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12577,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12577,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12577,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12577,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12577,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12577,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12577,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12577,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12577,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12577,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12577,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12577,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12577,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12577,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12577,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12577,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12577,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12577,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12577,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12577,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12577,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12577,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12577,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12577,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12577,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12577,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12577,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12577,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12577,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12577,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12577,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12577,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12577,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12577,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12577,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12577,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12577,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12577,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12577,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12577,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12577,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12577,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12577,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12577,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12577,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12577,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12577,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12577,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12577,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12577,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12577,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12577,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12577,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12577,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12577,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12577,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12577,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12577,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12577,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12577,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12577,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12577,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12577,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12577,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12577,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12577,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12577,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12577,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12577,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12577,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12577,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12577,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12577,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12577,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12577,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12577,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12577 : FrameRepair 12577 scalarRow12577 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12577Cells j).1 (repair12577Cells j).2.1
  endpoint_upper := fun j => ((repair12577Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12577Cells j).2.2

theorem repair12578Cells (j : Fin 43) :
    0 ≤ (scalarRow12578.table (sourceIndex j)).upper ∧
    (scalarRow12578.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12578.table (sourceIndex j)).centre) /
      (scalarRow12578.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12578.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12578,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12578,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12578,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12578,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12578,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12578,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12578,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12578,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12578,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12578,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12578,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12578,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12578,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12578,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12578,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12578,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12578,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12578,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12578,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12578,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12578,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12578,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12578,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12578,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12578,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12578,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12578,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12578,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12578,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12578,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12578,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12578,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12578,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12578,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12578,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12578,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12578,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12578,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12578,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12578,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12578,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12578,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12578,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12578,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12578,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12578,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12578,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12578,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12578,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12578,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12578,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12578,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12578,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12578,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12578,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12578,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12578,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12578,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12578,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12578,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12578,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12578,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12578,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12578,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12578,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12578,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12578,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12578,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12578,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12578,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12578,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12578,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12578,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12578,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12578,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12578,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12578,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12578,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12578,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12578,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12578,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12578,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12578,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12578,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12578,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12578,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12578 : FrameRepair 12578 scalarRow12578 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12578Cells j).1 (repair12578Cells j).2.1
  endpoint_upper := fun j => ((repair12578Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12578Cells j).2.2

theorem repair12579Cells (j : Fin 43) :
    0 ≤ (scalarRow12579.table (sourceIndex j)).upper ∧
    (scalarRow12579.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12579.table (sourceIndex j)).centre) /
      (scalarRow12579.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12579.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12579,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12579,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12579,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12579,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12579,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12579,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12579,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12579,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12579,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12579,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12579,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12579,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12579,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12579,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12579,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12579,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12579,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12579,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12579,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12579,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12579,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12579,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12579,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12579,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12579,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12579,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12579,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12579,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12579,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12579,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12579,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12579,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12579,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12579,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12579,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12579,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12579,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12579,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12579,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12579,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12579,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12579,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12579,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12579,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12579,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12579,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12579,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12579,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12579,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12579,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12579,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12579,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12579,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12579,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12579,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12579,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12579,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12579,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12579,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12579,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12579,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12579,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12579,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12579,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12579,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12579,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12579,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12579,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12579,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12579,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12579,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12579,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12579,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12579,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12579,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12579,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12579,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12579,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12579,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12579,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12579,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12579,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12579,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12579,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12579,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12579,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12579 : FrameRepair 12579 scalarRow12579 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12579Cells j).1 (repair12579Cells j).2.1
  endpoint_upper := fun j => ((repair12579Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12579Cells j).2.2

theorem repair12580Cells (j : Fin 43) :
    0 ≤ (scalarRow12580.table (sourceIndex j)).upper ∧
    (scalarRow12580.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12580.table (sourceIndex j)).centre) /
      (scalarRow12580.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12580.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12580,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12580,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12580,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12580,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12580,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12580,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12580,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12580,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12580,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12580,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12580,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12580,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12580,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12580,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12580,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12580,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12580,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12580,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12580,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12580,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12580,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12580,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12580,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12580,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12580,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12580,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12580,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12580,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12580,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12580,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12580,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12580,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12580,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12580,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12580,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12580,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12580,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12580,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12580,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12580,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12580,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12580,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12580,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12580,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12580,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12580,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12580,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12580,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12580,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12580,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12580,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12580,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12580,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12580,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12580,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12580,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12580,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12580,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12580,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12580,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12580,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12580,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12580,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12580,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12580,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12580,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12580,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12580,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12580,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12580,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12580,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12580,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12580,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12580,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12580,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12580,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12580,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12580,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12580,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12580,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12580,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12580,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12580,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12580,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12580,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12580,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12580 : FrameRepair 12580 scalarRow12580 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12580Cells j).1 (repair12580Cells j).2.1
  endpoint_upper := fun j => ((repair12580Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12580Cells j).2.2

theorem repair12581Cells (j : Fin 43) :
    0 ≤ (scalarRow12581.table (sourceIndex j)).upper ∧
    (scalarRow12581.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12581.table (sourceIndex j)).centre) /
      (scalarRow12581.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12581.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12581,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12581,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12581,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12581,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12581,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12581,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12581,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12581,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12581,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12581,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12581,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12581,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12581,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12581,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12581,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12581,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12581,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12581,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12581,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12581,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12581,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12581,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12581,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12581,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12581,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12581,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12581,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12581,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12581,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12581,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12581,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12581,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12581,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12581,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12581,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12581,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12581,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12581,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12581,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12581,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12581,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12581,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12581,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12581,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12581,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12581,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12581,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12581,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12581,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12581,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12581,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12581,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12581,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12581,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12581,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12581,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12581,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12581,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12581,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12581,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12581,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12581,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12581,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12581,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12581,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12581,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12581,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12581,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12581,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12581,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12581,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12581,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12581,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12581,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12581,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12581,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12581,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12581,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12581,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12581,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12581,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12581,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12581,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12581,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12581,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12581,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12581 : FrameRepair 12581 scalarRow12581 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12581Cells j).1 (repair12581Cells j).2.1
  endpoint_upper := fun j => ((repair12581Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12581Cells j).2.2

theorem repair12582Cells (j : Fin 43) :
    0 ≤ (scalarRow12582.table (sourceIndex j)).upper ∧
    (scalarRow12582.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12582.table (sourceIndex j)).centre) /
      (scalarRow12582.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12582.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12582,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12582,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12582,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12582,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12582,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12582,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12582,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12582,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12582,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12582,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12582,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12582,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12582,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12582,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12582,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12582,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12582,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12582,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12582,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12582,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12582,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12582,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12582,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12582,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12582,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12582,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12582,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12582,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12582,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12582,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12582,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12582,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12582,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12582,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12582,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12582,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12582,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12582,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12582,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12582,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12582,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12582,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12582,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12582,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12582,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12582,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12582,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12582,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12582,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12582,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12582,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12582,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12582,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12582,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12582,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12582,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12582,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12582,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12582,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12582,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12582,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12582,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12582,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12582,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12582,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12582,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12582,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12582,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12582,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12582,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12582,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12582,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12582,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12582,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12582,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12582,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12582,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12582,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12582,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12582,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12582,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12582,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12582,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12582,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12582,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12582,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12582 : FrameRepair 12582 scalarRow12582 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12582Cells j).1 (repair12582Cells j).2.1
  endpoint_upper := fun j => ((repair12582Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12582Cells j).2.2

theorem repair12583Cells (j : Fin 43) :
    0 ≤ (scalarRow12583.table (sourceIndex j)).upper ∧
    (scalarRow12583.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12583.table (sourceIndex j)).centre) /
      (scalarRow12583.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12583.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12583,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12583,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12583,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12583,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12583,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12583,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12583,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12583,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12583,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12583,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12583,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12583,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12583,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12583,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12583,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12583,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12583,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12583,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12583,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12583,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12583,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12583,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12583,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12583,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12583,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12583,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12583,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12583,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12583,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12583,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12583,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12583,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12583,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12583,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12583,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12583,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12583,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12583,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12583,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12583,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12583,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12583,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12583,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12583,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12583,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12583,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12583,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12583,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12583,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12583,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12583,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12583,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12583,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12583,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12583,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12583,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12583,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12583,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12583,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12583,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12583,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12583,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12583,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12583,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12583,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12583,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12583,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12583,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12583,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12583,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12583,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12583,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12583,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12583,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12583,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12583,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12583,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12583,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12583,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12583,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12583,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12583,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12583,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12583,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12583,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12583,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12583 : FrameRepair 12583 scalarRow12583 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12583Cells j).1 (repair12583Cells j).2.1
  endpoint_upper := fun j => ((repair12583Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12583Cells j).2.2

theorem repair12584Cells (j : Fin 43) :
    0 ≤ (scalarRow12584.table (sourceIndex j)).upper ∧
    (scalarRow12584.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12584.table (sourceIndex j)).centre) /
      (scalarRow12584.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12584.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12584,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12584,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12584,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12584,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12584,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12584,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12584,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12584,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12584,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12584,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12584,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12584,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12584,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12584,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12584,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12584,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12584,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12584,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12584,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12584,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12584,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12584,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12584,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12584,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12584,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12584,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12584,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12584,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12584,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12584,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12584,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12584,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12584,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12584,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12584,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12584,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12584,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12584,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12584,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12584,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12584,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12584,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12584,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12584,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12584,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12584,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12584,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12584,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12584,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12584,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12584,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12584,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12584,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12584,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12584,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12584,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12584,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12584,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12584,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12584,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12584,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12584,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12584,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12584,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12584,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12584,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12584,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12584,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12584,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12584,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12584,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12584,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12584,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12584,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12584,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12584,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12584,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12584,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12584,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12584,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12584,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12584,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12584,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12584,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12584,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12584,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12584 : FrameRepair 12584 scalarRow12584 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12584Cells j).1 (repair12584Cells j).2.1
  endpoint_upper := fun j => ((repair12584Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12584Cells j).2.2

theorem repair12585Cells (j : Fin 43) :
    0 ≤ (scalarRow12585.table (sourceIndex j)).upper ∧
    (scalarRow12585.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12585.table (sourceIndex j)).centre) /
      (scalarRow12585.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12585.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12585,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12585,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12585,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12585,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12585,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12585,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12585,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12585,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12585,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12585,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12585,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12585,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12585,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12585,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12585,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12585,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12585,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12585,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12585,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12585,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12585,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12585,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12585,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12585,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12585,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12585,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12585,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12585,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12585,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12585,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12585,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12585,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12585,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12585,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12585,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12585,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12585,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12585,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12585,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12585,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12585,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12585,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12585,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12585,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12585,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12585,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12585,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12585,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12585,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12585,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12585,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12585,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12585,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12585,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12585,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12585,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12585,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12585,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12585,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12585,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12585,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12585,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12585,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12585,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12585,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12585,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12585,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12585,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12585,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12585,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12585,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12585,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12585,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12585,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12585,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12585,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12585,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12585,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12585,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12585,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12585,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12585,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12585,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12585,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12585,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12585,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12585 : FrameRepair 12585 scalarRow12585 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12585Cells j).1 (repair12585Cells j).2.1
  endpoint_upper := fun j => ((repair12585Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12585Cells j).2.2

theorem repair12586Cells (j : Fin 43) :
    0 ≤ (scalarRow12586.table (sourceIndex j)).upper ∧
    (scalarRow12586.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12586.table (sourceIndex j)).centre) /
      (scalarRow12586.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12586.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12586,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12586,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12586,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12586,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12586,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12586,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12586,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12586,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12586,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12586,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12586,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12586,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12586,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12586,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12586,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12586,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12586,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12586,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12586,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12586,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12586,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12586,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12586,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12586,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12586,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12586,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12586,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12586,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12586,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12586,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12586,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12586,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12586,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12586,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12586,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12586,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12586,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12586,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12586,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12586,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12586,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12586,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12586,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12586,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12586,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12586,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12586,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12586,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12586,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12586,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12586,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12586,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12586,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12586,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12586,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12586,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12586,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12586,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12586,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12586,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12586,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12586,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12586,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12586,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12586,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12586,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12586,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12586,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12586,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12586,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12586,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12586,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12586,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12586,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12586,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12586,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12586,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12586,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12586,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12586,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12586,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12586,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12586,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12586,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12586,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12586,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12586 : FrameRepair 12586 scalarRow12586 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12586Cells j).1 (repair12586Cells j).2.1
  endpoint_upper := fun j => ((repair12586Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12586Cells j).2.2

theorem repair12587Cells (j : Fin 43) :
    0 ≤ (scalarRow12587.table (sourceIndex j)).upper ∧
    (scalarRow12587.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12587.table (sourceIndex j)).centre) /
      (scalarRow12587.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12587.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12587,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12587,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12587,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12587,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12587,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12587,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12587,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12587,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12587,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12587,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12587,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12587,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12587,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12587,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12587,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12587,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12587,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12587,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12587,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12587,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12587,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12587,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12587,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12587,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12587,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12587,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12587,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12587,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12587,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12587,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12587,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12587,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12587,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12587,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12587,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12587,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12587,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12587,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12587,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12587,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12587,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12587,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12587,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12587,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12587,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12587,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12587,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12587,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12587,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12587,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12587,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12587,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12587,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12587,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12587,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12587,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12587,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12587,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12587,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12587,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12587,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12587,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12587,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12587,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12587,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12587,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12587,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12587,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12587,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12587,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12587,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12587,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12587,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12587,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12587,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12587,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12587,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12587,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12587,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12587,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12587,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12587,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12587,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12587,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12587,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12587,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12587 : FrameRepair 12587 scalarRow12587 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12587Cells j).1 (repair12587Cells j).2.1
  endpoint_upper := fun j => ((repair12587Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12587Cells j).2.2

theorem repair12588Cells (j : Fin 43) :
    0 ≤ (scalarRow12588.table (sourceIndex j)).upper ∧
    (scalarRow12588.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12588.table (sourceIndex j)).centre) /
      (scalarRow12588.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12588.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12588,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12588,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12588,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12588,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12588,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12588,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12588,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12588,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12588,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12588,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12588,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12588,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12588,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12588,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12588,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12588,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12588,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12588,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12588,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12588,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12588,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12588,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12588,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12588,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12588,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12588,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12588,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12588,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12588,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12588,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12588,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12588,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12588,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12588,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12588,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12588,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12588,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12588,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12588,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12588,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12588,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12588,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12588,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12588,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12588,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12588,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12588,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12588,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12588,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12588,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12588,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12588,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12588,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12588,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12588,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12588,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12588,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12588,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12588,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12588,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12588,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12588,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12588,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12588,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12588,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12588,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12588,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12588,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12588,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12588,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12588,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12588,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12588,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12588,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12588,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12588,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12588,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12588,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12588,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12588,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12588,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12588,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12588,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12588,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12588,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12588,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12588 : FrameRepair 12588 scalarRow12588 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12588Cells j).1 (repair12588Cells j).2.1
  endpoint_upper := fun j => ((repair12588Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12588Cells j).2.2

theorem repair12589Cells (j : Fin 43) :
    0 ≤ (scalarRow12589.table (sourceIndex j)).upper ∧
    (scalarRow12589.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12589.table (sourceIndex j)).centre) /
      (scalarRow12589.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12589.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12589,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12589,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12589,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12589,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12589,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12589,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12589,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12589,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12589,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12589,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12589,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12589,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12589,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12589,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12589,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12589,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12589,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12589,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12589,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12589,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12589,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12589,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12589,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12589,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12589,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12589,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12589,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12589,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12589,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12589,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12589,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12589,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12589,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12589,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12589,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12589,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12589,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12589,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12589,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12589,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12589,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12589,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12589,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12589,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12589,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12589,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12589,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12589,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12589,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12589,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12589,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12589,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12589,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12589,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12589,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12589,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12589,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12589,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12589,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12589,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12589,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12589,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12589,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12589,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12589,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12589,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12589,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12589,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12589,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12589,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12589,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12589,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12589,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12589,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12589,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12589,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12589,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12589,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12589,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12589,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12589,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12589,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12589,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12589,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12589,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12589,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12589 : FrameRepair 12589 scalarRow12589 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12589Cells j).1 (repair12589Cells j).2.1
  endpoint_upper := fun j => ((repair12589Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12589Cells j).2.2

theorem repair12590Cells (j : Fin 43) :
    0 ≤ (scalarRow12590.table (sourceIndex j)).upper ∧
    (scalarRow12590.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12590.table (sourceIndex j)).centre) /
      (scalarRow12590.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12590.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12590,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12590,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12590,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12590,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12590,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12590,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12590,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12590,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12590,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12590,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12590,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12590,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12590,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12590,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12590,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12590,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12590,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12590,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12590,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12590,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12590,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12590,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12590,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12590,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12590,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12590,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12590,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12590,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12590,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12590,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12590,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12590,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12590,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12590,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12590,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12590,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12590,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12590,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12590,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12590,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12590,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12590,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12590,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12590,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12590,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12590,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12590,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12590,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12590,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12590,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12590,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12590,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12590,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12590,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12590,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12590,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12590,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12590,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12590,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12590,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12590,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12590,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12590,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12590,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12590,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12590,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12590,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12590,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12590,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12590,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12590,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12590,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12590,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12590,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12590,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12590,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12590,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12590,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12590,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12590,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12590,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12590,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12590,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12590,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12590,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12590,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12590 : FrameRepair 12590 scalarRow12590 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12590Cells j).1 (repair12590Cells j).2.1
  endpoint_upper := fun j => ((repair12590Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12590Cells j).2.2

theorem repair12591Cells (j : Fin 43) :
    0 ≤ (scalarRow12591.table (sourceIndex j)).upper ∧
    (scalarRow12591.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12591.table (sourceIndex j)).centre) /
      (scalarRow12591.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12591.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12591,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12591,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12591,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12591,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12591,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12591,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12591,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12591,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12591,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12591,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12591,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12591,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12591,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12591,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12591,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12591,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12591,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12591,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12591,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12591,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12591,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12591,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12591,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12591,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12591,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12591,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12591,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12591,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12591,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12591,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12591,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12591,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12591,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12591,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12591,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12591,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12591,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12591,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12591,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12591,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12591,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12591,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12591,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12591,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12591,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12591,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12591,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12591,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12591,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12591,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12591,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12591,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12591,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12591,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12591,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12591,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12591,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12591,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12591,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12591,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12591,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12591,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12591,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12591,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12591,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12591,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12591,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12591,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12591,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12591,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12591,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12591,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12591,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12591,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12591,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12591,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12591,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12591,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12591,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12591,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12591,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12591,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12591,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12591,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12591,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12591,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12591 : FrameRepair 12591 scalarRow12591 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12591Cells j).1 (repair12591Cells j).2.1
  endpoint_upper := fun j => ((repair12591Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12591Cells j).2.2

theorem repair12592Cells (j : Fin 43) :
    0 ≤ (scalarRow12592.table (sourceIndex j)).upper ∧
    (scalarRow12592.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12592.table (sourceIndex j)).centre) /
      (scalarRow12592.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12592.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12592,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12592,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12592,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12592,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12592,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12592,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12592,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12592,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12592,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12592,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12592,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12592,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12592,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12592,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12592,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12592,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12592,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12592,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12592,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12592,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12592,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12592,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12592,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12592,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12592,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12592,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12592,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12592,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12592,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12592,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12592,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12592,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12592,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12592,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12592,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12592,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12592,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12592,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12592,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12592,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12592,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12592,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12592,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12592,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12592,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12592,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12592,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12592,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12592,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12592,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12592,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12592,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12592,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12592,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12592,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12592,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12592,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12592,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12592,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12592,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12592,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12592,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12592,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12592,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12592,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12592,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12592,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12592,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12592,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12592,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12592,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12592,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12592,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12592,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12592,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12592,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12592,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12592,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12592,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12592,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12592,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12592,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12592,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12592,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12592,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12592,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12592 : FrameRepair 12592 scalarRow12592 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12592Cells j).1 (repair12592Cells j).2.1
  endpoint_upper := fun j => ((repair12592Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12592Cells j).2.2

theorem repair12593Cells (j : Fin 43) :
    0 ≤ (scalarRow12593.table (sourceIndex j)).upper ∧
    (scalarRow12593.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12593.table (sourceIndex j)).centre) /
      (scalarRow12593.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12593.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12593,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12593,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12593,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12593,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12593,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12593,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12593,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12593,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12593,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12593,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12593,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12593,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12593,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12593,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12593,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12593,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12593,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12593,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12593,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12593,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12593,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12593,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12593,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12593,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12593,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12593,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12593,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12593,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12593,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12593,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12593,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12593,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12593,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12593,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12593,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12593,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12593,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12593,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12593,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12593,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12593,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12593,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12593,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12593,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12593,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12593,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12593,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12593,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12593,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12593,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12593,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12593,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12593,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12593,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12593,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12593,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12593,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12593,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12593,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12593,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12593,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12593,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12593,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12593,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12593,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12593,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12593,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12593,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12593,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12593,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12593,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12593,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12593,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12593,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12593,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12593,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12593,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12593,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12593,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12593,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12593,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12593,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12593,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12593,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12593,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12593,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12593 : FrameRepair 12593 scalarRow12593 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12593Cells j).1 (repair12593Cells j).2.1
  endpoint_upper := fun j => ((repair12593Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12593Cells j).2.2

theorem repair12594Cells (j : Fin 43) :
    0 ≤ (scalarRow12594.table (sourceIndex j)).upper ∧
    (scalarRow12594.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12594.table (sourceIndex j)).centre) /
      (scalarRow12594.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12594.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12594,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12594,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12594,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12594,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12594,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12594,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12594,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12594,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12594,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12594,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12594,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12594,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12594,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12594,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12594,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12594,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12594,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12594,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12594,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12594,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12594,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12594,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12594,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12594,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12594,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12594,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12594,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12594,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12594,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12594,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12594,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12594,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12594,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12594,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12594,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12594,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12594,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12594,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12594,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12594,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12594,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12594,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12594,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12594,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12594,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12594,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12594,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12594,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12594,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12594,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12594,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12594,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12594,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12594,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12594,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12594,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12594,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12594,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12594,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12594,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12594,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12594,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12594,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12594,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12594,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12594,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12594,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12594,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12594,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12594,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12594,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12594,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12594,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12594,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12594,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12594,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12594,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12594,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12594,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12594,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12594,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12594,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12594,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12594,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12594,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12594,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12594 : FrameRepair 12594 scalarRow12594 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12594Cells j).1 (repair12594Cells j).2.1
  endpoint_upper := fun j => ((repair12594Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12594Cells j).2.2

theorem repair12595Cells (j : Fin 43) :
    0 ≤ (scalarRow12595.table (sourceIndex j)).upper ∧
    (scalarRow12595.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12595.table (sourceIndex j)).centre) /
      (scalarRow12595.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12595.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12595,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12595,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12595,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12595,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12595,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12595,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12595,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12595,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12595,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12595,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12595,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12595,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12595,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12595,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12595,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12595,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12595,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12595,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12595,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12595,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12595,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12595,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12595,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12595,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12595,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12595,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12595,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12595,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12595,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12595,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12595,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12595,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12595,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12595,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12595,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12595,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12595,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12595,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12595,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12595,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12595,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12595,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12595,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12595,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12595,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12595,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12595,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12595,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12595,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12595,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12595,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12595,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12595,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12595,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12595,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12595,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12595,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12595,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12595,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12595,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12595,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12595,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12595,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12595,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12595,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12595,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12595,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12595,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12595,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12595,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12595,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12595,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12595,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12595,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12595,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12595,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12595,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12595,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12595,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12595,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12595,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12595,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12595,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12595,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12595,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12595,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12595 : FrameRepair 12595 scalarRow12595 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12595Cells j).1 (repair12595Cells j).2.1
  endpoint_upper := fun j => ((repair12595Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12595Cells j).2.2

theorem repair12596Cells (j : Fin 43) :
    0 ≤ (scalarRow12596.table (sourceIndex j)).upper ∧
    (scalarRow12596.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12596.table (sourceIndex j)).centre) /
      (scalarRow12596.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12596.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12596,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12596,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12596,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12596,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12596,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12596,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12596,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12596,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12596,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12596,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12596,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12596,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12596,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12596,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12596,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12596,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12596,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12596,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12596,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12596,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12596,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12596,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12596,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12596,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12596,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12596,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12596,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12596,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12596,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12596,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12596,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12596,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12596,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12596,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12596,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12596,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12596,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12596,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12596,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12596,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12596,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12596,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12596,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12596,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12596,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12596,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12596,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12596,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12596,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12596,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12596,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12596,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12596,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12596,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12596,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12596,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12596,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12596,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12596,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12596,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12596,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12596,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12596,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12596,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12596,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12596,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12596,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12596,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12596,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12596,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12596,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12596,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12596,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12596,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12596,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12596,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12596,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12596,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12596,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12596,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12596,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12596,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12596,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12596,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12596,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12596,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12596 : FrameRepair 12596 scalarRow12596 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12596Cells j).1 (repair12596Cells j).2.1
  endpoint_upper := fun j => ((repair12596Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12596Cells j).2.2

theorem repair12597Cells (j : Fin 43) :
    0 ≤ (scalarRow12597.table (sourceIndex j)).upper ∧
    (scalarRow12597.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12597.table (sourceIndex j)).centre) /
      (scalarRow12597.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12597.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12597,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12597,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12597,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12597,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12597,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12597,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12597,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12597,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12597,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12597,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12597,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12597,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12597,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12597,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12597,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12597,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12597,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12597,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12597,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12597,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12597,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12597,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12597,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12597,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12597,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12597,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12597,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12597,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12597,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12597,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12597,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12597,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12597,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12597,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12597,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12597,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12597,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12597,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12597,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12597,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12597,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12597,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12597,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12597,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12597,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12597,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12597,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12597,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12597,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12597,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12597,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12597,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12597,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12597,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12597,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12597,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12597,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12597,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12597,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12597,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12597,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12597,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12597,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12597,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12597,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12597,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12597,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12597,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12597,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12597,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12597,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12597,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12597,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12597,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12597,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12597,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12597,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12597,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12597,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12597,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12597,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12597,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12597,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12597,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12597,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12597,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12597 : FrameRepair 12597 scalarRow12597 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12597Cells j).1 (repair12597Cells j).2.1
  endpoint_upper := fun j => ((repair12597Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12597Cells j).2.2

theorem repair12598Cells (j : Fin 43) :
    0 ≤ (scalarRow12598.table (sourceIndex j)).upper ∧
    (scalarRow12598.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12598.table (sourceIndex j)).centre) /
      (scalarRow12598.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12598.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12598,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12598,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12598,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12598,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12598,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12598,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12598,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12598,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12598,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12598,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12598,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12598,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12598,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12598,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12598,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12598,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12598,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12598,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12598,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12598,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12598,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12598,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12598,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12598,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12598,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12598,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12598,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12598,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12598,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12598,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12598,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12598,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12598,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12598,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12598,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12598,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12598,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12598,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12598,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12598,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12598,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12598,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12598,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12598,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12598,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12598,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12598,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12598,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12598,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12598,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12598,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12598,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12598,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12598,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12598,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12598,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12598,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12598,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12598,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12598,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12598,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12598,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12598,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12598,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12598,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12598,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12598,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12598,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12598,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12598,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12598,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12598,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12598,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12598,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12598,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12598,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12598,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12598,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12598,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12598,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12598,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12598,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12598,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12598,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12598,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12598,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12598 : FrameRepair 12598 scalarRow12598 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12598Cells j).1 (repair12598Cells j).2.1
  endpoint_upper := fun j => ((repair12598Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12598Cells j).2.2

theorem repair12599Cells (j : Fin 43) :
    0 ≤ (scalarRow12599.table (sourceIndex j)).upper ∧
    (scalarRow12599.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12599.table (sourceIndex j)).centre) /
      (scalarRow12599.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12599.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12599,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12599,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12599,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12599,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12599,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12599,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12599,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12599,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12599,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12599,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12599,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12599,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12599,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12599,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12599,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12599,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12599,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12599,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12599,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12599,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12599,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12599,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12599,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12599,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12599,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12599,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12599,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12599,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12599,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12599,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12599,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12599,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12599,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12599,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12599,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12599,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12599,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12599,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12599,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12599,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12599,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12599,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12599,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12599,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12599,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12599,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12599,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12599,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12599,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12599,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12599,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12599,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12599,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12599,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12599,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12599,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12599,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12599,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12599,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12599,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12599,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12599,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12599,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12599,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12599,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12599,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12599,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12599,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12599,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12599,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12599,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12599,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12599,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12599,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12599,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12599,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12599,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12599,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12599,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12599,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12599,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12599,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12599,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12599,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12599,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12599,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12599 : FrameRepair 12599 scalarRow12599 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12599Cells j).1 (repair12599Cells j).2.1
  endpoint_upper := fun j => ((repair12599Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12599Cells j).2.2

end BstLean.Part269
