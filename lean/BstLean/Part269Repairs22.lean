import BstLean.Part269Rows22
import BstLean.Part269RepairCommon
namespace BstLean.Part269
open Real Set BstLean.Part255 BstLean.Part263 BstLean.Part264
theorem repair12900Cells (j : Fin 43) :
    0 ≤ (scalarRow12900.table (sourceIndex j)).upper ∧
    (scalarRow12900.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12900.table (sourceIndex j)).centre) /
      (scalarRow12900.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12900.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12900,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12900,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12900,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12900,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12900,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12900,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12900,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12900,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12900,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12900,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12900,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12900,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12900,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12900,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12900,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12900,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12900,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12900,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12900,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12900,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12900,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12900,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12900,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12900,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12900,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12900,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12900,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12900,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12900,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12900,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12900,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12900,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12900,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12900,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12900,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12900,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12900,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12900,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12900,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12900,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12900,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12900,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12900,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12900,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12900,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12900,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12900,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12900,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12900,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12900,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12900,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12900,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12900,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12900,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12900,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12900,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12900,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12900,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12900,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12900,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12900,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12900,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12900,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12900,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12900,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12900,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12900,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12900,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12900,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12900,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12900,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12900,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12900,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12900,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12900,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12900,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12900,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12900,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12900,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12900,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12900,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12900,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12900,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12900,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12900,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12900,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12900 : FrameRepair 12900 scalarRow12900 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12900Cells j).1 (repair12900Cells j).2.1
  endpoint_upper := fun j => ((repair12900Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12900Cells j).2.2

theorem repair12901Cells (j : Fin 43) :
    0 ≤ (scalarRow12901.table (sourceIndex j)).upper ∧
    (scalarRow12901.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12901.table (sourceIndex j)).centre) /
      (scalarRow12901.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12901.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12901,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12901,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12901,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12901,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12901,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12901,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12901,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12901,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12901,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12901,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12901,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12901,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12901,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12901,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12901,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12901,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12901,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12901,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12901,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12901,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12901,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12901,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12901,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12901,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12901,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12901,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12901,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12901,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12901,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12901,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12901,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12901,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12901,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12901,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12901,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12901,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12901,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12901,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12901,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12901,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12901,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12901,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12901,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12901,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12901,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12901,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12901,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12901,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12901,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12901,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12901,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12901,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12901,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12901,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12901,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12901,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12901,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12901,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12901,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12901,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12901,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12901,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12901,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12901,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12901,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12901,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12901,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12901,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12901,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12901,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12901,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12901,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12901,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12901,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12901,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12901,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12901,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12901,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12901,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12901,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12901,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12901,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12901,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12901,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12901,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12901,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12901 : FrameRepair 12901 scalarRow12901 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12901Cells j).1 (repair12901Cells j).2.1
  endpoint_upper := fun j => ((repair12901Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12901Cells j).2.2

theorem repair12902Cells (j : Fin 43) :
    0 ≤ (scalarRow12902.table (sourceIndex j)).upper ∧
    (scalarRow12902.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12902.table (sourceIndex j)).centre) /
      (scalarRow12902.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12902.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12902,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12902,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12902,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12902,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12902,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12902,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12902,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12902,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12902,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12902,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12902,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12902,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12902,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12902,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12902,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12902,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12902,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12902,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12902,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12902,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12902,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12902,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12902,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12902,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12902,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12902,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12902,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12902,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12902,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12902,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12902,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12902,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12902,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12902,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12902,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12902,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12902,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12902,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12902,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12902,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12902,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12902,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12902,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12902,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12902,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12902,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12902,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12902,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12902,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12902,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12902,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12902,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12902,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12902,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12902,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12902,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12902,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12902,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12902,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12902,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12902,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12902,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12902,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12902,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12902,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12902,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12902,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12902,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12902,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12902,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12902,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12902,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12902,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12902,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12902,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12902,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12902,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12902,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12902,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12902,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12902,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12902,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12902,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12902,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12902,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12902,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12902 : FrameRepair 12902 scalarRow12902 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12902Cells j).1 (repair12902Cells j).2.1
  endpoint_upper := fun j => ((repair12902Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12902Cells j).2.2

theorem repair12903Cells (j : Fin 43) :
    0 ≤ (scalarRow12903.table (sourceIndex j)).upper ∧
    (scalarRow12903.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12903.table (sourceIndex j)).centre) /
      (scalarRow12903.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12903.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12903,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12903,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12903,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12903,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12903,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12903,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12903,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12903,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12903,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12903,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12903,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12903,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12903,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12903,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12903,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12903,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12903,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12903,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12903,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12903,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12903,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12903,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12903,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12903,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12903,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12903,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12903,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12903,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12903,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12903,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12903,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12903,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12903,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12903,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12903,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12903,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12903,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12903,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12903,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12903,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12903,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12903,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12903,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12903,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12903,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12903,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12903,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12903,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12903,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12903,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12903,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12903,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12903,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12903,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12903,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12903,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12903,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12903,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12903,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12903,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12903,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12903,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12903,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12903,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12903,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12903,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12903,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12903,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12903,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12903,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12903,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12903,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12903,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12903,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12903,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12903,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12903,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12903,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12903,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12903,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12903,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12903,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12903,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12903,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12903,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12903,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12903 : FrameRepair 12903 scalarRow12903 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12903Cells j).1 (repair12903Cells j).2.1
  endpoint_upper := fun j => ((repair12903Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12903Cells j).2.2

theorem repair12904Cells (j : Fin 43) :
    0 ≤ (scalarRow12904.table (sourceIndex j)).upper ∧
    (scalarRow12904.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12904.table (sourceIndex j)).centre) /
      (scalarRow12904.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12904.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12904,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12904,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12904,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12904,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12904,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12904,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12904,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12904,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12904,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12904,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12904,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12904,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12904,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12904,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12904,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12904,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12904,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12904,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12904,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12904,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12904,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12904,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12904,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12904,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12904,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12904,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12904,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12904,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12904,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12904,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12904,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12904,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12904,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12904,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12904,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12904,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12904,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12904,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12904,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12904,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12904,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12904,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12904,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12904,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12904,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12904,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12904,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12904,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12904,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12904,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12904,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12904,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12904,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12904,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12904,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12904,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12904,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12904,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12904,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12904,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12904,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12904,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12904,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12904,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12904,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12904,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12904,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12904,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12904,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12904,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12904,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12904,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12904,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12904,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12904,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12904,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12904,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12904,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12904,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12904,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12904,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12904,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12904,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12904,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12904,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12904,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12904 : FrameRepair 12904 scalarRow12904 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12904Cells j).1 (repair12904Cells j).2.1
  endpoint_upper := fun j => ((repair12904Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12904Cells j).2.2

theorem repair12905Cells (j : Fin 43) :
    0 ≤ (scalarRow12905.table (sourceIndex j)).upper ∧
    (scalarRow12905.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12905.table (sourceIndex j)).centre) /
      (scalarRow12905.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12905.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12905,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12905,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12905,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12905,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12905,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12905,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12905,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12905,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12905,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12905,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12905,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12905,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12905,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12905,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12905,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12905,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12905,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12905,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12905,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12905,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12905,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12905,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12905,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12905,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12905,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12905,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12905,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12905,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12905,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12905,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12905,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12905,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12905,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12905,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12905,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12905,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12905,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12905,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12905,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12905,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12905,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12905,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12905,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12905,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12905,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12905,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12905,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12905,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12905,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12905,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12905,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12905,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12905,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12905,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12905,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12905,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12905,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12905,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12905,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12905,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12905,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12905,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12905,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12905,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12905,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12905,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12905,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12905,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12905,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12905,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12905,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12905,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12905,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12905,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12905,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12905,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12905,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12905,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12905,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12905,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12905,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12905,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12905,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12905,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12905,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12905,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12905 : FrameRepair 12905 scalarRow12905 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12905Cells j).1 (repair12905Cells j).2.1
  endpoint_upper := fun j => ((repair12905Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12905Cells j).2.2

theorem repair12906Cells (j : Fin 43) :
    0 ≤ (scalarRow12906.table (sourceIndex j)).upper ∧
    (scalarRow12906.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12906.table (sourceIndex j)).centre) /
      (scalarRow12906.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12906.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12906,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12906,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12906,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12906,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12906,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12906,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12906,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12906,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12906,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12906,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12906,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12906,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12906,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12906,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12906,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12906,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12906,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12906,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12906,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12906,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12906,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12906,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12906,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12906,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12906,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12906,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12906,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12906,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12906,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12906,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12906,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12906,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12906,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12906,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12906,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12906,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12906,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12906,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12906,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12906,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12906,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12906,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12906,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12906,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12906,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12906,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12906,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12906,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12906,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12906,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12906,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12906,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12906,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12906,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12906,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12906,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12906,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12906,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12906,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12906,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12906,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12906,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12906,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12906,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12906,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12906,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12906,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12906,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12906,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12906,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12906,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12906,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12906,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12906,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12906,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12906,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12906,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12906,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12906,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12906,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12906,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12906,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12906,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12906,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12906,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12906,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12906 : FrameRepair 12906 scalarRow12906 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12906Cells j).1 (repair12906Cells j).2.1
  endpoint_upper := fun j => ((repair12906Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12906Cells j).2.2

theorem repair12907Cells (j : Fin 43) :
    0 ≤ (scalarRow12907.table (sourceIndex j)).upper ∧
    (scalarRow12907.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12907.table (sourceIndex j)).centre) /
      (scalarRow12907.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12907.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12907,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12907,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12907,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12907,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12907,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12907,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12907,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12907,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12907,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12907,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12907,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12907,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12907,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12907,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12907,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12907,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12907,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12907,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12907,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12907,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12907,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12907,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12907,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12907,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12907,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12907,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12907,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12907,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12907,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12907,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12907,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12907,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12907,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12907,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12907,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12907,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12907,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12907,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12907,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12907,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12907,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12907,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12907,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12907,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12907,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12907,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12907,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12907,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12907,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12907,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12907,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12907,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12907,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12907,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12907,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12907,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12907,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12907,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12907,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12907,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12907,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12907,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12907,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12907,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12907,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12907,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12907,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12907,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12907,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12907,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12907,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12907,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12907,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12907,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12907,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12907,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12907,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12907,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12907,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12907,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12907,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12907,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12907,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12907,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12907,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12907,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12907 : FrameRepair 12907 scalarRow12907 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12907Cells j).1 (repair12907Cells j).2.1
  endpoint_upper := fun j => ((repair12907Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12907Cells j).2.2

theorem repair12908Cells (j : Fin 43) :
    0 ≤ (scalarRow12908.table (sourceIndex j)).upper ∧
    (scalarRow12908.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12908.table (sourceIndex j)).centre) /
      (scalarRow12908.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12908.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12908,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12908,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12908,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12908,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12908,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12908,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12908,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12908,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12908,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12908,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12908,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12908,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12908,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12908,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12908,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12908,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12908,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12908,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12908,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12908,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12908,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12908,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12908,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12908,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12908,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12908,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12908,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12908,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12908,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12908,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12908,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12908,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12908,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12908,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12908,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12908,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12908,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12908,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12908,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12908,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12908,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12908,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12908,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12908,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12908,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12908,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12908,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12908,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12908,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12908,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12908,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12908,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12908,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12908,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12908,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12908,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12908,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12908,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12908,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12908,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12908,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12908,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12908,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12908,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12908,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12908,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12908,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12908,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12908,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12908,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12908,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12908,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12908,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12908,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12908,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12908,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12908,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12908,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12908,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12908,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12908,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12908,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12908,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12908,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12908,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12908,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12908 : FrameRepair 12908 scalarRow12908 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12908Cells j).1 (repair12908Cells j).2.1
  endpoint_upper := fun j => ((repair12908Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12908Cells j).2.2

theorem repair12909Cells (j : Fin 43) :
    0 ≤ (scalarRow12909.table (sourceIndex j)).upper ∧
    (scalarRow12909.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12909.table (sourceIndex j)).centre) /
      (scalarRow12909.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12909.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12909,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12909,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12909,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12909,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12909,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12909,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12909,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12909,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12909,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12909,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12909,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12909,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12909,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12909,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12909,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12909,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12909,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12909,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12909,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12909,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12909,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12909,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12909,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12909,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12909,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12909,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12909,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12909,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12909,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12909,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12909,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12909,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12909,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12909,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12909,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12909,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12909,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12909,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12909,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12909,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12909,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12909,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12909,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12909,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12909,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12909,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12909,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12909,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12909,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12909,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12909,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12909,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12909,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12909,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12909,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12909,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12909,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12909,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12909,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12909,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12909,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12909,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12909,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12909,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12909,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12909,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12909,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12909,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12909,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12909,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12909,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12909,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12909,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12909,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12909,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12909,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12909,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12909,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12909,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12909,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12909,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12909,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12909,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12909,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12909,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12909,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12909 : FrameRepair 12909 scalarRow12909 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12909Cells j).1 (repair12909Cells j).2.1
  endpoint_upper := fun j => ((repair12909Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12909Cells j).2.2

theorem repair12910Cells (j : Fin 43) :
    0 ≤ (scalarRow12910.table (sourceIndex j)).upper ∧
    (scalarRow12910.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12910.table (sourceIndex j)).centre) /
      (scalarRow12910.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12910.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12910,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12910,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12910,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12910,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12910,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12910,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12910,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12910,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12910,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12910,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12910,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12910,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12910,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12910,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12910,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12910,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12910,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12910,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12910,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12910,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12910,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12910,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12910,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12910,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12910,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12910,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12910,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12910,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12910,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12910,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12910,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12910,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12910,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12910,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12910,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12910,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12910,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12910,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12910,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12910,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12910,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12910,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12910,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12910,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12910,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12910,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12910,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12910,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12910,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12910,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12910,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12910,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12910,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12910,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12910,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12910,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12910,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12910,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12910,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12910,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12910,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12910,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12910,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12910,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12910,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12910,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12910,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12910,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12910,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12910,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12910,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12910,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12910,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12910,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12910,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12910,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12910,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12910,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12910,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12910,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12910,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12910,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12910,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12910,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12910,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12910,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12910 : FrameRepair 12910 scalarRow12910 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12910Cells j).1 (repair12910Cells j).2.1
  endpoint_upper := fun j => ((repair12910Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12910Cells j).2.2

theorem repair12911Cells (j : Fin 43) :
    0 ≤ (scalarRow12911.table (sourceIndex j)).upper ∧
    (scalarRow12911.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12911.table (sourceIndex j)).centre) /
      (scalarRow12911.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12911.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12911,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12911,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12911,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12911,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12911,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12911,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12911,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12911,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12911,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12911,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12911,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12911,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12911,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12911,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12911,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12911,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12911,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12911,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12911,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12911,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12911,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12911,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12911,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12911,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12911,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12911,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12911,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12911,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12911,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12911,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12911,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12911,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12911,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12911,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12911,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12911,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12911,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12911,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12911,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12911,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12911,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12911,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12911,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12911,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12911,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12911,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12911,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12911,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12911,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12911,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12911,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12911,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12911,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12911,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12911,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12911,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12911,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12911,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12911,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12911,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12911,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12911,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12911,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12911,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12911,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12911,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12911,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12911,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12911,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12911,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12911,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12911,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12911,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12911,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12911,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12911,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12911,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12911,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12911,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12911,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12911,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12911,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12911,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12911,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12911,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12911,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12911 : FrameRepair 12911 scalarRow12911 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12911Cells j).1 (repair12911Cells j).2.1
  endpoint_upper := fun j => ((repair12911Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12911Cells j).2.2

theorem repair12912Cells (j : Fin 43) :
    0 ≤ (scalarRow12912.table (sourceIndex j)).upper ∧
    (scalarRow12912.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12912.table (sourceIndex j)).centre) /
      (scalarRow12912.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12912.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12912,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12912,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12912,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12912,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12912,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12912,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12912,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12912,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12912,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12912,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12912,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12912,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12912,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12912,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12912,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12912,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12912,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12912,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12912,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12912,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12912,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12912,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12912,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12912,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12912,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12912,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12912,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12912,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12912,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12912,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12912,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12912,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12912,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12912,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12912,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12912,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12912,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12912,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12912,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12912,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12912,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12912,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12912,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12912,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12912,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12912,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12912,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12912,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12912,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12912,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12912,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12912,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12912,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12912,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12912,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12912,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12912,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12912,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12912,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12912,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12912,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12912,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12912,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12912,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12912,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12912,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12912,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12912,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12912,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12912,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12912,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12912,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12912,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12912,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12912,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12912,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12912,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12912,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12912,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12912,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12912,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12912,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12912,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12912,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12912,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12912,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12912 : FrameRepair 12912 scalarRow12912 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12912Cells j).1 (repair12912Cells j).2.1
  endpoint_upper := fun j => ((repair12912Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12912Cells j).2.2

theorem repair12913Cells (j : Fin 43) :
    0 ≤ (scalarRow12913.table (sourceIndex j)).upper ∧
    (scalarRow12913.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12913.table (sourceIndex j)).centre) /
      (scalarRow12913.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12913.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12913,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12913,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12913,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12913,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12913,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12913,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12913,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12913,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12913,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12913,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12913,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12913,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12913,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12913,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12913,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12913,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12913,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12913,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12913,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12913,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12913,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12913,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12913,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12913,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12913,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12913,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12913,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12913,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12913,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12913,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12913,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12913,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12913,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12913,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12913,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12913,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12913,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12913,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12913,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12913,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12913,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12913,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12913,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12913,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12913,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12913,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12913,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12913,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12913,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12913,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12913,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12913,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12913,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12913,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12913,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12913,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12913,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12913,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12913,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12913,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12913,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12913,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12913,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12913,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12913,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12913,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12913,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12913,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12913,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12913,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12913,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12913,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12913,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12913,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12913,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12913,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12913,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12913,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12913,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12913,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12913,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12913,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12913,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12913,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12913,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12913,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12913 : FrameRepair 12913 scalarRow12913 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12913Cells j).1 (repair12913Cells j).2.1
  endpoint_upper := fun j => ((repair12913Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12913Cells j).2.2

theorem repair12914Cells (j : Fin 43) :
    0 ≤ (scalarRow12914.table (sourceIndex j)).upper ∧
    (scalarRow12914.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12914.table (sourceIndex j)).centre) /
      (scalarRow12914.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12914.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12914,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12914,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12914,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12914,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12914,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12914,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12914,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12914,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12914,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12914,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12914,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12914,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12914,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12914,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12914,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12914,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12914,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12914,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12914,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12914,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12914,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12914,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12914,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12914,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12914,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12914,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12914,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12914,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12914,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12914,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12914,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12914,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12914,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12914,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12914,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12914,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12914,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12914,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12914,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12914,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12914,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12914,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12914,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12914,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12914,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12914,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12914,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12914,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12914,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12914,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12914,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12914,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12914,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12914,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12914,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12914,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12914,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12914,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12914,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12914,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12914,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12914,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12914,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12914,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12914,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12914,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12914,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12914,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12914,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12914,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12914,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12914,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12914,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12914,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12914,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12914,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12914,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12914,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12914,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12914,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12914,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12914,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12914,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12914,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12914,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12914,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12914 : FrameRepair 12914 scalarRow12914 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12914Cells j).1 (repair12914Cells j).2.1
  endpoint_upper := fun j => ((repair12914Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12914Cells j).2.2

theorem repair12915Cells (j : Fin 43) :
    0 ≤ (scalarRow12915.table (sourceIndex j)).upper ∧
    (scalarRow12915.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12915.table (sourceIndex j)).centre) /
      (scalarRow12915.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12915.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12915,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12915,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12915,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12915,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12915,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12915,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12915,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12915,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12915,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12915,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12915,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12915,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12915,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12915,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12915,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12915,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12915,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12915,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12915,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12915,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12915,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12915,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12915,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12915,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12915,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12915,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12915,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12915,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12915,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12915,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12915,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12915,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12915,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12915,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12915,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12915,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12915,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12915,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12915,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12915,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12915,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12915,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12915,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12915,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12915,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12915,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12915,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12915,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12915,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12915,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12915,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12915,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12915,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12915,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12915,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12915,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12915,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12915,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12915,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12915,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12915,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12915,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12915,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12915,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12915,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12915,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12915,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12915,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12915,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12915,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12915,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12915,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12915,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12915,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12915,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12915,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12915,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12915,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12915,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12915,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12915,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12915,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12915,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12915,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12915,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12915,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12915 : FrameRepair 12915 scalarRow12915 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12915Cells j).1 (repair12915Cells j).2.1
  endpoint_upper := fun j => ((repair12915Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12915Cells j).2.2

theorem repair12916Cells (j : Fin 43) :
    0 ≤ (scalarRow12916.table (sourceIndex j)).upper ∧
    (scalarRow12916.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12916.table (sourceIndex j)).centre) /
      (scalarRow12916.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12916.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12916,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12916,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12916,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12916,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12916,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12916,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12916,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12916,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12916,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12916,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12916,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12916,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12916,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12916,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12916,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12916,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12916,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12916,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12916,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12916,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12916,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12916,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12916,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12916,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12916,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12916,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12916,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12916,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12916,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12916,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12916,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12916,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12916,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12916,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12916,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12916,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12916,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12916,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12916,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12916,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12916,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12916,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12916,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12916,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12916,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12916,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12916,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12916,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12916,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12916,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12916,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12916,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12916,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12916,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12916,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12916,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12916,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12916,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12916,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12916,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12916,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12916,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12916,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12916,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12916,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12916,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12916,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12916,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12916,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12916,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12916,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12916,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12916,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12916,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12916,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12916,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12916,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12916,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12916,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12916,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12916,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12916,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12916,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12916,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12916,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12916,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12916 : FrameRepair 12916 scalarRow12916 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12916Cells j).1 (repair12916Cells j).2.1
  endpoint_upper := fun j => ((repair12916Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12916Cells j).2.2

theorem repair12917Cells (j : Fin 43) :
    0 ≤ (scalarRow12917.table (sourceIndex j)).upper ∧
    (scalarRow12917.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12917.table (sourceIndex j)).centre) /
      (scalarRow12917.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12917.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12917,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12917,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12917,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12917,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12917,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12917,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12917,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12917,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12917,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12917,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12917,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12917,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12917,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12917,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12917,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12917,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12917,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12917,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12917,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12917,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12917,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12917,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12917,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12917,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12917,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12917,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12917,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12917,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12917,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12917,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12917,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12917,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12917,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12917,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12917,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12917,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12917,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12917,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12917,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12917,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12917,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12917,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12917,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12917,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12917,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12917,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12917,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12917,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12917,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12917,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12917,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12917,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12917,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12917,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12917,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12917,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12917,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12917,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12917,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12917,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12917,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12917,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12917,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12917,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12917,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12917,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12917,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12917,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12917,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12917,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12917,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12917,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12917,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12917,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12917,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12917,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12917,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12917,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12917,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12917,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12917,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12917,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12917,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12917,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12917,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12917,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12917 : FrameRepair 12917 scalarRow12917 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12917Cells j).1 (repair12917Cells j).2.1
  endpoint_upper := fun j => ((repair12917Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12917Cells j).2.2

theorem repair12918Cells (j : Fin 43) :
    0 ≤ (scalarRow12918.table (sourceIndex j)).upper ∧
    (scalarRow12918.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12918.table (sourceIndex j)).centre) /
      (scalarRow12918.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12918.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12918,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12918,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12918,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12918,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12918,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12918,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12918,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12918,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12918,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12918,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12918,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12918,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12918,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12918,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12918,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12918,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12918,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12918,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12918,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12918,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12918,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12918,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12918,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12918,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12918,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12918,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12918,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12918,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12918,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12918,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12918,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12918,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12918,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12918,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12918,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12918,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12918,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12918,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12918,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12918,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12918,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12918,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12918,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12918,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12918,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12918,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12918,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12918,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12918,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12918,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12918,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12918,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12918,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12918,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12918,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12918,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12918,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12918,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12918,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12918,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12918,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12918,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12918,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12918,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12918,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12918,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12918,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12918,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12918,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12918,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12918,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12918,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12918,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12918,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12918,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12918,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12918,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12918,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12918,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12918,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12918,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12918,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12918,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12918,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12918,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12918,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12918 : FrameRepair 12918 scalarRow12918 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12918Cells j).1 (repair12918Cells j).2.1
  endpoint_upper := fun j => ((repair12918Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12918Cells j).2.2

theorem repair12919Cells (j : Fin 43) :
    0 ≤ (scalarRow12919.table (sourceIndex j)).upper ∧
    (scalarRow12919.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12919.table (sourceIndex j)).centre) /
      (scalarRow12919.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12919.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12919,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12919,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12919,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12919,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12919,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12919,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12919,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12919,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12919,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12919,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12919,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12919,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12919,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12919,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12919,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12919,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12919,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12919,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12919,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12919,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12919,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12919,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12919,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12919,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12919,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12919,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12919,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12919,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12919,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12919,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12919,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12919,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12919,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12919,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12919,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12919,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12919,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12919,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12919,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12919,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12919,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12919,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12919,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12919,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12919,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12919,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12919,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12919,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12919,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12919,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12919,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12919,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12919,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12919,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12919,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12919,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12919,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12919,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12919,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12919,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12919,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12919,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12919,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12919,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12919,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12919,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12919,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12919,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12919,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12919,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12919,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12919,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12919,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12919,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12919,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12919,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12919,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12919,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12919,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12919,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12919,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12919,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12919,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12919,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12919,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12919,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12919 : FrameRepair 12919 scalarRow12919 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12919Cells j).1 (repair12919Cells j).2.1
  endpoint_upper := fun j => ((repair12919Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12919Cells j).2.2

theorem repair12920Cells (j : Fin 43) :
    0 ≤ (scalarRow12920.table (sourceIndex j)).upper ∧
    (scalarRow12920.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12920.table (sourceIndex j)).centre) /
      (scalarRow12920.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12920.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12920,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12920,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12920,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12920,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12920,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12920,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12920,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12920,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12920,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12920,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12920,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12920,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12920,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12920,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12920,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12920,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12920,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12920,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12920,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12920,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12920,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12920,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12920,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12920,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12920,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12920,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12920,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12920,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12920,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12920,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12920,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12920,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12920,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12920,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12920,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12920,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12920,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12920,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12920,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12920,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12920,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12920,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12920,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12920,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12920,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12920,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12920,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12920,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12920,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12920,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12920,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12920,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12920,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12920,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12920,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12920,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12920,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12920,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12920,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12920,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12920,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12920,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12920,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12920,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12920,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12920,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12920,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12920,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12920,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12920,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12920,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12920,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12920,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12920,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12920,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12920,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12920,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12920,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12920,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12920,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12920,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12920,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12920,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12920,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12920,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12920,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12920 : FrameRepair 12920 scalarRow12920 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12920Cells j).1 (repair12920Cells j).2.1
  endpoint_upper := fun j => ((repair12920Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12920Cells j).2.2

theorem repair12921Cells (j : Fin 43) :
    0 ≤ (scalarRow12921.table (sourceIndex j)).upper ∧
    (scalarRow12921.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12921.table (sourceIndex j)).centre) /
      (scalarRow12921.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12921.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12921,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12921,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12921,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12921,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12921,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12921,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12921,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12921,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12921,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12921,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12921,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12921,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12921,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12921,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12921,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12921,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12921,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12921,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12921,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12921,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12921,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12921,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12921,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12921,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12921,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12921,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12921,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12921,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12921,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12921,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12921,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12921,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12921,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12921,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12921,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12921,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12921,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12921,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12921,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12921,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12921,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12921,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12921,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12921,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12921,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12921,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12921,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12921,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12921,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12921,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12921,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12921,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12921,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12921,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12921,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12921,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12921,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12921,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12921,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12921,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12921,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12921,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12921,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12921,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12921,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12921,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12921,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12921,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12921,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12921,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12921,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12921,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12921,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12921,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12921,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12921,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12921,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12921,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12921,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12921,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12921,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12921,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12921,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12921,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12921,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12921,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12921 : FrameRepair 12921 scalarRow12921 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12921Cells j).1 (repair12921Cells j).2.1
  endpoint_upper := fun j => ((repair12921Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12921Cells j).2.2

theorem repair12922Cells (j : Fin 43) :
    0 ≤ (scalarRow12922.table (sourceIndex j)).upper ∧
    (scalarRow12922.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12922.table (sourceIndex j)).centre) /
      (scalarRow12922.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12922.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12922,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12922,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12922,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12922,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12922,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12922,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12922,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12922,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12922,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12922,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12922,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12922,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12922,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12922,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12922,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12922,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12922,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12922,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12922,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12922,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12922,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12922,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12922,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12922,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12922,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12922,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12922,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12922,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12922,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12922,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12922,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12922,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12922,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12922,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12922,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12922,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12922,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12922,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12922,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12922,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12922,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12922,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12922,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12922,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12922,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12922,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12922,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12922,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12922,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12922,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12922,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12922,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12922,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12922,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12922,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12922,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12922,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12922,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12922,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12922,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12922,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12922,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12922,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12922,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12922,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12922,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12922,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12922,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12922,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12922,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12922,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12922,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12922,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12922,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12922,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12922,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12922,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12922,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12922,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12922,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12922,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12922,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12922,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12922,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12922,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12922,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12922 : FrameRepair 12922 scalarRow12922 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12922Cells j).1 (repair12922Cells j).2.1
  endpoint_upper := fun j => ((repair12922Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12922Cells j).2.2

theorem repair12923Cells (j : Fin 43) :
    0 ≤ (scalarRow12923.table (sourceIndex j)).upper ∧
    (scalarRow12923.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12923.table (sourceIndex j)).centre) /
      (scalarRow12923.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12923.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12923,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12923,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12923,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12923,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12923,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12923,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12923,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12923,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12923,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12923,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12923,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12923,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12923,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12923,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12923,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12923,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12923,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12923,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12923,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12923,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12923,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12923,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12923,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12923,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12923,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12923,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12923,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12923,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12923,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12923,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12923,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12923,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12923,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12923,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12923,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12923,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12923,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12923,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12923,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12923,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12923,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12923,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12923,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12923,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12923,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12923,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12923,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12923,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12923,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12923,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12923,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12923,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12923,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12923,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12923,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12923,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12923,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12923,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12923,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12923,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12923,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12923,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12923,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12923,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12923,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12923,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12923,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12923,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12923,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12923,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12923,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12923,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12923,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12923,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12923,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12923,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12923,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12923,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12923,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12923,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12923,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12923,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12923,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12923,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12923,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12923,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12923 : FrameRepair 12923 scalarRow12923 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12923Cells j).1 (repair12923Cells j).2.1
  endpoint_upper := fun j => ((repair12923Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12923Cells j).2.2

theorem repair12924Cells (j : Fin 43) :
    0 ≤ (scalarRow12924.table (sourceIndex j)).upper ∧
    (scalarRow12924.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12924.table (sourceIndex j)).centre) /
      (scalarRow12924.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12924.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12924,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12924,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12924,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12924,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12924,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12924,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12924,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12924,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12924,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12924,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12924,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12924,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12924,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12924,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12924,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12924,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12924,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12924,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12924,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12924,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12924,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12924,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12924,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12924,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12924,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12924,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12924,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12924,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12924,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12924,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12924,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12924,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12924,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12924,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12924,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12924,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12924,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12924,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12924,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12924,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12924,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12924,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12924,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12924,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12924,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12924,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12924,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12924,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12924,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12924,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12924,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12924,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12924,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12924,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12924,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12924,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12924,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12924,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12924,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12924,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12924,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12924,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12924,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12924,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12924,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12924,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12924,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12924,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12924,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12924,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12924,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12924,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12924,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12924,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12924,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12924,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12924,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12924,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12924,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12924,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12924,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12924,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12924,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12924,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12924,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12924,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12924 : FrameRepair 12924 scalarRow12924 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12924Cells j).1 (repair12924Cells j).2.1
  endpoint_upper := fun j => ((repair12924Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12924Cells j).2.2

end BstLean.Part269
