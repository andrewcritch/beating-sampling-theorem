import BstLean.Part269Rows1
import BstLean.Part269RepairCommon
namespace BstLean.Part269
open Real Set BstLean.Part255 BstLean.Part263 BstLean.Part264
theorem repair12375Cells (j : Fin 43) :
    0 ≤ (scalarRow12375.table (sourceIndex j)).upper ∧
    (scalarRow12375.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12375.table (sourceIndex j)).centre) /
      (scalarRow12375.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12375.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12375,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12375,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12375,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12375,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12375,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12375,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12375,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12375,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12375,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12375,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12375,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12375,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12375,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12375,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12375,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12375,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12375,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12375,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12375,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12375,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12375,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12375,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12375,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12375,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12375,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12375,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12375,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12375,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12375,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12375,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12375,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12375,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12375,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12375,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12375,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12375,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12375,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12375,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12375,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12375,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12375,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12375,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12375,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12375,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12375,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12375,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12375,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12375,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12375,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12375,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12375,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12375,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12375,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12375,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12375,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12375,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12375,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12375,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12375,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12375,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12375,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12375,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12375,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12375,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12375,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12375,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12375,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12375,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12375,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12375,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12375,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12375,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12375,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12375,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12375,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12375,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12375,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12375,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12375,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12375,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12375,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12375,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12375,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12375,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12375,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12375,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12375 : FrameRepair 12375 scalarRow12375 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12375Cells j).1 (repair12375Cells j).2.1
  endpoint_upper := fun j => ((repair12375Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12375Cells j).2.2

theorem repair12376Cells (j : Fin 43) :
    0 ≤ (scalarRow12376.table (sourceIndex j)).upper ∧
    (scalarRow12376.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12376.table (sourceIndex j)).centre) /
      (scalarRow12376.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12376.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12376,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12376,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12376,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12376,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12376,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12376,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12376,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12376,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12376,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12376,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12376,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12376,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12376,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12376,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12376,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12376,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12376,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12376,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12376,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12376,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12376,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12376,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12376,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12376,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12376,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12376,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12376,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12376,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12376,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12376,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12376,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12376,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12376,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12376,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12376,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12376,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12376,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12376,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12376,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12376,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12376,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12376,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12376,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12376,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12376,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12376,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12376,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12376,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12376,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12376,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12376,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12376,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12376,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12376,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12376,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12376,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12376,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12376,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12376,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12376,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12376,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12376,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12376,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12376,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12376,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12376,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12376,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12376,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12376,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12376,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12376,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12376,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12376,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12376,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12376,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12376,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12376,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12376,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12376,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12376,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12376,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12376,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12376,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12376,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12376,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12376,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12376 : FrameRepair 12376 scalarRow12376 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12376Cells j).1 (repair12376Cells j).2.1
  endpoint_upper := fun j => ((repair12376Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12376Cells j).2.2

theorem repair12377Cells (j : Fin 43) :
    0 ≤ (scalarRow12377.table (sourceIndex j)).upper ∧
    (scalarRow12377.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12377.table (sourceIndex j)).centre) /
      (scalarRow12377.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12377.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12377,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12377,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12377,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12377,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12377,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12377,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12377,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12377,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12377,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12377,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12377,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12377,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12377,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12377,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12377,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12377,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12377,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12377,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12377,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12377,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12377,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12377,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12377,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12377,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12377,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12377,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12377,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12377,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12377,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12377,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12377,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12377,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12377,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12377,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12377,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12377,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12377,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12377,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12377,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12377,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12377,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12377,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12377,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12377,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12377,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12377,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12377,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12377,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12377,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12377,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12377,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12377,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12377,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12377,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12377,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12377,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12377,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12377,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12377,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12377,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12377,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12377,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12377,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12377,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12377,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12377,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12377,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12377,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12377,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12377,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12377,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12377,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12377,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12377,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12377,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12377,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12377,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12377,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12377,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12377,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12377,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12377,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12377,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12377,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12377,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12377,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12377 : FrameRepair 12377 scalarRow12377 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12377Cells j).1 (repair12377Cells j).2.1
  endpoint_upper := fun j => ((repair12377Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12377Cells j).2.2

theorem repair12378Cells (j : Fin 43) :
    0 ≤ (scalarRow12378.table (sourceIndex j)).upper ∧
    (scalarRow12378.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12378.table (sourceIndex j)).centre) /
      (scalarRow12378.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12378.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12378,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12378,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12378,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12378,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12378,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12378,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12378,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12378,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12378,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12378,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12378,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12378,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12378,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12378,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12378,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12378,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12378,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12378,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12378,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12378,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12378,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12378,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12378,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12378,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12378,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12378,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12378,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12378,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12378,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12378,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12378,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12378,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12378,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12378,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12378,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12378,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12378,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12378,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12378,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12378,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12378,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12378,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12378,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12378,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12378,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12378,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12378,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12378,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12378,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12378,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12378,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12378,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12378,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12378,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12378,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12378,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12378,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12378,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12378,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12378,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12378,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12378,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12378,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12378,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12378,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12378,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12378,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12378,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12378,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12378,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12378,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12378,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12378,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12378,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12378,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12378,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12378,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12378,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12378,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12378,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12378,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12378,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12378,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12378,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12378,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12378,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12378 : FrameRepair 12378 scalarRow12378 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12378Cells j).1 (repair12378Cells j).2.1
  endpoint_upper := fun j => ((repair12378Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12378Cells j).2.2

theorem repair12379Cells (j : Fin 43) :
    0 ≤ (scalarRow12379.table (sourceIndex j)).upper ∧
    (scalarRow12379.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12379.table (sourceIndex j)).centre) /
      (scalarRow12379.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12379.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12379,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12379,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12379,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12379,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12379,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12379,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12379,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12379,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12379,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12379,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12379,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12379,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12379,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12379,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12379,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12379,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12379,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12379,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12379,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12379,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12379,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12379,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12379,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12379,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12379,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12379,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12379,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12379,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12379,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12379,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12379,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12379,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12379,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12379,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12379,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12379,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12379,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12379,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12379,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12379,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12379,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12379,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12379,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12379,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12379,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12379,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12379,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12379,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12379,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12379,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12379,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12379,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12379,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12379,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12379,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12379,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12379,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12379,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12379,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12379,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12379,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12379,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12379,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12379,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12379,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12379,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12379,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12379,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12379,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12379,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12379,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12379,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12379,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12379,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12379,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12379,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12379,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12379,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12379,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12379,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12379,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12379,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12379,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12379,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12379,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12379,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12379 : FrameRepair 12379 scalarRow12379 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12379Cells j).1 (repair12379Cells j).2.1
  endpoint_upper := fun j => ((repair12379Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12379Cells j).2.2

theorem repair12380Cells (j : Fin 43) :
    0 ≤ (scalarRow12380.table (sourceIndex j)).upper ∧
    (scalarRow12380.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12380.table (sourceIndex j)).centre) /
      (scalarRow12380.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12380.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12380,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12380,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12380,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12380,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12380,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12380,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12380,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12380,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12380,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12380,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12380,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12380,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12380,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12380,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12380,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12380,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12380,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12380,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12380,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12380,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12380,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12380,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12380,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12380,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12380,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12380,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12380,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12380,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12380,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12380,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12380,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12380,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12380,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12380,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12380,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12380,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12380,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12380,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12380,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12380,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12380,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12380,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12380,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12380,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12380,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12380,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12380,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12380,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12380,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12380,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12380,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12380,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12380,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12380,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12380,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12380,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12380,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12380,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12380,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12380,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12380,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12380,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12380,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12380,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12380,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12380,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12380,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12380,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12380,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12380,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12380,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12380,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12380,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12380,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12380,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12380,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12380,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12380,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12380,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12380,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12380,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12380,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12380,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12380,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12380,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12380,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12380 : FrameRepair 12380 scalarRow12380 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12380Cells j).1 (repair12380Cells j).2.1
  endpoint_upper := fun j => ((repair12380Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12380Cells j).2.2

theorem repair12381Cells (j : Fin 43) :
    0 ≤ (scalarRow12381.table (sourceIndex j)).upper ∧
    (scalarRow12381.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12381.table (sourceIndex j)).centre) /
      (scalarRow12381.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12381.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12381,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12381,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12381,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12381,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12381,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12381,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12381,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12381,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12381,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12381,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12381,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12381,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12381,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12381,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12381,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12381,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12381,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12381,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12381,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12381,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12381,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12381,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12381,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12381,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12381,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12381,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12381,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12381,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12381,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12381,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12381,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12381,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12381,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12381,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12381,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12381,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12381,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12381,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12381,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12381,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12381,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12381,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12381,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12381,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12381,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12381,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12381,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12381,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12381,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12381,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12381,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12381,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12381,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12381,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12381,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12381,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12381,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12381,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12381,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12381,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12381,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12381,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12381,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12381,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12381,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12381,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12381,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12381,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12381,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12381,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12381,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12381,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12381,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12381,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12381,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12381,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12381,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12381,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12381,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12381,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12381,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12381,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12381,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12381,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12381,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12381,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12381 : FrameRepair 12381 scalarRow12381 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12381Cells j).1 (repair12381Cells j).2.1
  endpoint_upper := fun j => ((repair12381Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12381Cells j).2.2

theorem repair12382Cells (j : Fin 43) :
    0 ≤ (scalarRow12382.table (sourceIndex j)).upper ∧
    (scalarRow12382.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12382.table (sourceIndex j)).centre) /
      (scalarRow12382.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12382.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12382,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12382,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12382,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12382,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12382,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12382,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12382,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12382,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12382,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12382,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12382,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12382,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12382,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12382,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12382,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12382,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12382,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12382,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12382,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12382,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12382,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12382,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12382,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12382,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12382,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12382,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12382,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12382,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12382,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12382,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12382,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12382,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12382,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12382,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12382,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12382,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12382,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12382,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12382,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12382,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12382,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12382,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12382,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12382,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12382,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12382,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12382,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12382,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12382,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12382,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12382,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12382,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12382,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12382,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12382,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12382,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12382,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12382,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12382,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12382,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12382,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12382,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12382,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12382,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12382,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12382,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12382,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12382,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12382,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12382,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12382,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12382,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12382,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12382,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12382,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12382,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12382,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12382,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12382,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12382,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12382,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12382,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12382,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12382,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12382,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12382,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12382 : FrameRepair 12382 scalarRow12382 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12382Cells j).1 (repair12382Cells j).2.1
  endpoint_upper := fun j => ((repair12382Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12382Cells j).2.2

theorem repair12383Cells (j : Fin 43) :
    0 ≤ (scalarRow12383.table (sourceIndex j)).upper ∧
    (scalarRow12383.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12383.table (sourceIndex j)).centre) /
      (scalarRow12383.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12383.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12383,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12383,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12383,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12383,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12383,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12383,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12383,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12383,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12383,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12383,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12383,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12383,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12383,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12383,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12383,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12383,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12383,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12383,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12383,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12383,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12383,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12383,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12383,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12383,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12383,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12383,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12383,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12383,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12383,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12383,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12383,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12383,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12383,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12383,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12383,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12383,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12383,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12383,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12383,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12383,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12383,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12383,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12383,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12383,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12383,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12383,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12383,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12383,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12383,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12383,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12383,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12383,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12383,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12383,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12383,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12383,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12383,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12383,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12383,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12383,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12383,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12383,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12383,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12383,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12383,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12383,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12383,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12383,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12383,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12383,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12383,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12383,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12383,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12383,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12383,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12383,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12383,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12383,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12383,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12383,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12383,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12383,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12383,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12383,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12383,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12383,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12383 : FrameRepair 12383 scalarRow12383 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12383Cells j).1 (repair12383Cells j).2.1
  endpoint_upper := fun j => ((repair12383Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12383Cells j).2.2

theorem repair12384Cells (j : Fin 43) :
    0 ≤ (scalarRow12384.table (sourceIndex j)).upper ∧
    (scalarRow12384.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12384.table (sourceIndex j)).centre) /
      (scalarRow12384.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12384.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12384,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12384,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12384,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12384,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12384,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12384,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12384,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12384,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12384,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12384,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12384,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12384,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12384,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12384,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12384,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12384,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12384,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12384,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12384,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12384,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12384,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12384,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12384,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12384,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12384,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12384,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12384,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12384,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12384,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12384,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12384,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12384,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12384,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12384,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12384,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12384,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12384,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12384,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12384,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12384,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12384,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12384,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12384,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12384,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12384,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12384,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12384,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12384,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12384,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12384,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12384,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12384,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12384,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12384,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12384,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12384,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12384,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12384,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12384,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12384,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12384,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12384,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12384,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12384,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12384,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12384,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12384,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12384,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12384,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12384,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12384,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12384,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12384,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12384,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12384,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12384,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12384,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12384,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12384,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12384,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12384,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12384,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12384,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12384,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12384,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12384,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12384 : FrameRepair 12384 scalarRow12384 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12384Cells j).1 (repair12384Cells j).2.1
  endpoint_upper := fun j => ((repair12384Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12384Cells j).2.2

theorem repair12385Cells (j : Fin 43) :
    0 ≤ (scalarRow12385.table (sourceIndex j)).upper ∧
    (scalarRow12385.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12385.table (sourceIndex j)).centre) /
      (scalarRow12385.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12385.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12385,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12385,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12385,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12385,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12385,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12385,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12385,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12385,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12385,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12385,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12385,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12385,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12385,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12385,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12385,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12385,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12385,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12385,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12385,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12385,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12385,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12385,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12385,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12385,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12385,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12385,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12385,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12385,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12385,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12385,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12385,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12385,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12385,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12385,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12385,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12385,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12385,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12385,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12385,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12385,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12385,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12385,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12385,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12385,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12385,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12385,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12385,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12385,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12385,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12385,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12385,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12385,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12385,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12385,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12385,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12385,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12385,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12385,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12385,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12385,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12385,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12385,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12385,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12385,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12385,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12385,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12385,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12385,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12385,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12385,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12385,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12385,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12385,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12385,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12385,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12385,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12385,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12385,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12385,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12385,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12385,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12385,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12385,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12385,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12385,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12385,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12385 : FrameRepair 12385 scalarRow12385 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12385Cells j).1 (repair12385Cells j).2.1
  endpoint_upper := fun j => ((repair12385Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12385Cells j).2.2

theorem repair12386Cells (j : Fin 43) :
    0 ≤ (scalarRow12386.table (sourceIndex j)).upper ∧
    (scalarRow12386.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12386.table (sourceIndex j)).centre) /
      (scalarRow12386.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12386.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12386,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12386,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12386,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12386,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12386,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12386,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12386,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12386,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12386,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12386,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12386,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12386,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12386,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12386,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12386,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12386,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12386,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12386,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12386,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12386,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12386,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12386,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12386,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12386,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12386,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12386,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12386,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12386,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12386,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12386,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12386,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12386,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12386,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12386,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12386,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12386,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12386,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12386,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12386,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12386,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12386,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12386,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12386,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12386,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12386,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12386,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12386,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12386,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12386,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12386,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12386,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12386,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12386,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12386,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12386,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12386,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12386,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12386,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12386,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12386,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12386,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12386,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12386,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12386,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12386,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12386,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12386,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12386,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12386,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12386,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12386,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12386,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12386,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12386,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12386,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12386,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12386,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12386,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12386,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12386,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12386,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12386,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12386,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12386,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12386,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12386,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12386 : FrameRepair 12386 scalarRow12386 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12386Cells j).1 (repair12386Cells j).2.1
  endpoint_upper := fun j => ((repair12386Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12386Cells j).2.2

theorem repair12387Cells (j : Fin 43) :
    0 ≤ (scalarRow12387.table (sourceIndex j)).upper ∧
    (scalarRow12387.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12387.table (sourceIndex j)).centre) /
      (scalarRow12387.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12387.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12387,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12387,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12387,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12387,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12387,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12387,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12387,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12387,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12387,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12387,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12387,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12387,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12387,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12387,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12387,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12387,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12387,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12387,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12387,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12387,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12387,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12387,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12387,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12387,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12387,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12387,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12387,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12387,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12387,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12387,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12387,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12387,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12387,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12387,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12387,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12387,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12387,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12387,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12387,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12387,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12387,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12387,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12387,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12387,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12387,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12387,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12387,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12387,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12387,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12387,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12387,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12387,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12387,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12387,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12387,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12387,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12387,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12387,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12387,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12387,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12387,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12387,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12387,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12387,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12387,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12387,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12387,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12387,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12387,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12387,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12387,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12387,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12387,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12387,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12387,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12387,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12387,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12387,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12387,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12387,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12387,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12387,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12387,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12387,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12387,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12387,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12387 : FrameRepair 12387 scalarRow12387 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12387Cells j).1 (repair12387Cells j).2.1
  endpoint_upper := fun j => ((repair12387Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12387Cells j).2.2

theorem repair12388Cells (j : Fin 43) :
    0 ≤ (scalarRow12388.table (sourceIndex j)).upper ∧
    (scalarRow12388.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12388.table (sourceIndex j)).centre) /
      (scalarRow12388.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12388.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12388,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12388,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12388,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12388,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12388,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12388,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12388,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12388,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12388,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12388,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12388,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12388,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12388,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12388,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12388,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12388,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12388,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12388,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12388,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12388,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12388,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12388,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12388,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12388,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12388,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12388,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12388,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12388,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12388,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12388,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12388,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12388,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12388,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12388,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12388,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12388,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12388,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12388,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12388,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12388,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12388,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12388,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12388,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12388,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12388,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12388,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12388,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12388,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12388,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12388,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12388,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12388,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12388,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12388,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12388,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12388,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12388,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12388,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12388,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12388,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12388,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12388,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12388,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12388,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12388,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12388,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12388,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12388,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12388,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12388,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12388,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12388,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12388,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12388,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12388,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12388,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12388,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12388,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12388,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12388,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12388,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12388,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12388,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12388,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12388,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12388,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12388 : FrameRepair 12388 scalarRow12388 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12388Cells j).1 (repair12388Cells j).2.1
  endpoint_upper := fun j => ((repair12388Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12388Cells j).2.2

theorem repair12389Cells (j : Fin 43) :
    0 ≤ (scalarRow12389.table (sourceIndex j)).upper ∧
    (scalarRow12389.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12389.table (sourceIndex j)).centre) /
      (scalarRow12389.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12389.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12389,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12389,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12389,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12389,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12389,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12389,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12389,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12389,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12389,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12389,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12389,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12389,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12389,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12389,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12389,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12389,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12389,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12389,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12389,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12389,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12389,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12389,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12389,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12389,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12389,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12389,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12389,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12389,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12389,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12389,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12389,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12389,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12389,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12389,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12389,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12389,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12389,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12389,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12389,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12389,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12389,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12389,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12389,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12389,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12389,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12389,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12389,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12389,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12389,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12389,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12389,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12389,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12389,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12389,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12389,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12389,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12389,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12389,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12389,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12389,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12389,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12389,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12389,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12389,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12389,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12389,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12389,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12389,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12389,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12389,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12389,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12389,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12389,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12389,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12389,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12389,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12389,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12389,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12389,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12389,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12389,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12389,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12389,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12389,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12389,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12389,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12389 : FrameRepair 12389 scalarRow12389 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12389Cells j).1 (repair12389Cells j).2.1
  endpoint_upper := fun j => ((repair12389Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12389Cells j).2.2

theorem repair12390Cells (j : Fin 43) :
    0 ≤ (scalarRow12390.table (sourceIndex j)).upper ∧
    (scalarRow12390.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12390.table (sourceIndex j)).centre) /
      (scalarRow12390.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12390.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12390,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12390,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12390,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12390,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12390,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12390,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12390,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12390,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12390,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12390,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12390,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12390,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12390,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12390,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12390,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12390,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12390,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12390,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12390,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12390,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12390,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12390,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12390,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12390,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12390,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12390,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12390,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12390,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12390,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12390,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12390,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12390,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12390,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12390,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12390,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12390,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12390,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12390,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12390,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12390,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12390,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12390,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12390,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12390,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12390,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12390,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12390,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12390,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12390,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12390,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12390,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12390,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12390,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12390,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12390,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12390,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12390,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12390,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12390,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12390,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12390,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12390,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12390,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12390,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12390,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12390,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12390,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12390,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12390,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12390,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12390,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12390,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12390,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12390,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12390,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12390,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12390,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12390,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12390,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12390,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12390,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12390,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12390,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12390,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12390,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12390,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12390 : FrameRepair 12390 scalarRow12390 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12390Cells j).1 (repair12390Cells j).2.1
  endpoint_upper := fun j => ((repair12390Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12390Cells j).2.2

theorem repair12391Cells (j : Fin 43) :
    0 ≤ (scalarRow12391.table (sourceIndex j)).upper ∧
    (scalarRow12391.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12391.table (sourceIndex j)).centre) /
      (scalarRow12391.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12391.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12391,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12391,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12391,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12391,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12391,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12391,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12391,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12391,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12391,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12391,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12391,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12391,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12391,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12391,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12391,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12391,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12391,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12391,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12391,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12391,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12391,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12391,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12391,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12391,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12391,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12391,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12391,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12391,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12391,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12391,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12391,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12391,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12391,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12391,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12391,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12391,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12391,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12391,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12391,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12391,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12391,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12391,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12391,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12391,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12391,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12391,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12391,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12391,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12391,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12391,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12391,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12391,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12391,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12391,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12391,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12391,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12391,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12391,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12391,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12391,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12391,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12391,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12391,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12391,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12391,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12391,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12391,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12391,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12391,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12391,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12391,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12391,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12391,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12391,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12391,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12391,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12391,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12391,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12391,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12391,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12391,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12391,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12391,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12391,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12391,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12391,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12391 : FrameRepair 12391 scalarRow12391 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12391Cells j).1 (repair12391Cells j).2.1
  endpoint_upper := fun j => ((repair12391Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12391Cells j).2.2

theorem repair12392Cells (j : Fin 43) :
    0 ≤ (scalarRow12392.table (sourceIndex j)).upper ∧
    (scalarRow12392.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12392.table (sourceIndex j)).centre) /
      (scalarRow12392.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12392.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12392,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12392,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12392,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12392,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12392,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12392,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12392,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12392,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12392,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12392,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12392,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12392,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12392,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12392,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12392,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12392,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12392,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12392,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12392,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12392,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12392,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12392,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12392,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12392,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12392,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12392,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12392,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12392,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12392,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12392,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12392,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12392,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12392,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12392,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12392,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12392,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12392,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12392,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12392,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12392,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12392,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12392,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12392,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12392,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12392,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12392,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12392,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12392,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12392,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12392,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12392,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12392,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12392,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12392,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12392,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12392,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12392,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12392,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12392,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12392,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12392,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12392,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12392,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12392,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12392,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12392,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12392,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12392,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12392,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12392,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12392,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12392,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12392,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12392,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12392,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12392,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12392,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12392,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12392,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12392,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12392,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12392,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12392,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12392,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12392,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12392,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12392 : FrameRepair 12392 scalarRow12392 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12392Cells j).1 (repair12392Cells j).2.1
  endpoint_upper := fun j => ((repair12392Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12392Cells j).2.2

theorem repair12393Cells (j : Fin 43) :
    0 ≤ (scalarRow12393.table (sourceIndex j)).upper ∧
    (scalarRow12393.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12393.table (sourceIndex j)).centre) /
      (scalarRow12393.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12393.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12393,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12393,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12393,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12393,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12393,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12393,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12393,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12393,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12393,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12393,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12393,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12393,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12393,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12393,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12393,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12393,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12393,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12393,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12393,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12393,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12393,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12393,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12393,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12393,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12393,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12393,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12393,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12393,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12393,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12393,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12393,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12393,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12393,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12393,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12393,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12393,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12393,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12393,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12393,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12393,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12393,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12393,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12393,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12393,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12393,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12393,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12393,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12393,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12393,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12393,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12393,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12393,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12393,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12393,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12393,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12393,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12393,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12393,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12393,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12393,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12393,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12393,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12393,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12393,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12393,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12393,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12393,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12393,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12393,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12393,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12393,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12393,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12393,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12393,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12393,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12393,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12393,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12393,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12393,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12393,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12393,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12393,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12393,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12393,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12393,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12393,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12393 : FrameRepair 12393 scalarRow12393 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12393Cells j).1 (repair12393Cells j).2.1
  endpoint_upper := fun j => ((repair12393Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12393Cells j).2.2

theorem repair12394Cells (j : Fin 43) :
    0 ≤ (scalarRow12394.table (sourceIndex j)).upper ∧
    (scalarRow12394.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12394.table (sourceIndex j)).centre) /
      (scalarRow12394.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12394.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12394,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12394,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12394,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12394,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12394,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12394,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12394,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12394,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12394,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12394,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12394,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12394,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12394,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12394,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12394,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12394,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12394,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12394,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12394,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12394,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12394,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12394,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12394,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12394,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12394,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12394,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12394,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12394,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12394,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12394,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12394,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12394,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12394,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12394,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12394,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12394,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12394,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12394,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12394,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12394,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12394,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12394,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12394,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12394,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12394,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12394,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12394,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12394,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12394,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12394,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12394,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12394,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12394,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12394,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12394,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12394,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12394,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12394,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12394,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12394,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12394,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12394,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12394,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12394,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12394,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12394,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12394,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12394,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12394,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12394,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12394,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12394,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12394,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12394,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12394,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12394,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12394,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12394,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12394,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12394,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12394,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12394,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12394,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12394,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12394,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12394,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12394 : FrameRepair 12394 scalarRow12394 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12394Cells j).1 (repair12394Cells j).2.1
  endpoint_upper := fun j => ((repair12394Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12394Cells j).2.2

theorem repair12395Cells (j : Fin 43) :
    0 ≤ (scalarRow12395.table (sourceIndex j)).upper ∧
    (scalarRow12395.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12395.table (sourceIndex j)).centre) /
      (scalarRow12395.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12395.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12395,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12395,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12395,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12395,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12395,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12395,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12395,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12395,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12395,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12395,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12395,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12395,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12395,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12395,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12395,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12395,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12395,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12395,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12395,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12395,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12395,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12395,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12395,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12395,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12395,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12395,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12395,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12395,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12395,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12395,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12395,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12395,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12395,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12395,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12395,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12395,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12395,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12395,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12395,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12395,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12395,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12395,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12395,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12395,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12395,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12395,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12395,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12395,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12395,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12395,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12395,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12395,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12395,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12395,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12395,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12395,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12395,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12395,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12395,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12395,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12395,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12395,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12395,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12395,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12395,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12395,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12395,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12395,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12395,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12395,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12395,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12395,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12395,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12395,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12395,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12395,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12395,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12395,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12395,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12395,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12395,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12395,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12395,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12395,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12395,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12395,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12395 : FrameRepair 12395 scalarRow12395 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12395Cells j).1 (repair12395Cells j).2.1
  endpoint_upper := fun j => ((repair12395Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12395Cells j).2.2

theorem repair12396Cells (j : Fin 43) :
    0 ≤ (scalarRow12396.table (sourceIndex j)).upper ∧
    (scalarRow12396.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12396.table (sourceIndex j)).centre) /
      (scalarRow12396.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12396.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12396,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12396,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12396,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12396,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12396,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12396,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12396,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12396,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12396,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12396,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12396,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12396,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12396,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12396,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12396,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12396,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12396,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12396,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12396,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12396,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12396,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12396,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12396,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12396,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12396,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12396,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12396,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12396,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12396,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12396,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12396,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12396,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12396,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12396,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12396,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12396,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12396,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12396,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12396,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12396,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12396,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12396,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12396,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12396,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12396,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12396,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12396,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12396,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12396,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12396,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12396,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12396,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12396,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12396,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12396,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12396,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12396,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12396,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12396,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12396,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12396,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12396,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12396,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12396,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12396,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12396,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12396,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12396,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12396,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12396,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12396,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12396,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12396,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12396,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12396,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12396,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12396,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12396,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12396,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12396,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12396,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12396,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12396,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12396,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12396,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12396,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12396 : FrameRepair 12396 scalarRow12396 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12396Cells j).1 (repair12396Cells j).2.1
  endpoint_upper := fun j => ((repair12396Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12396Cells j).2.2

theorem repair12397Cells (j : Fin 43) :
    0 ≤ (scalarRow12397.table (sourceIndex j)).upper ∧
    (scalarRow12397.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12397.table (sourceIndex j)).centre) /
      (scalarRow12397.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12397.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12397,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12397,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12397,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12397,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12397,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12397,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12397,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12397,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12397,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12397,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12397,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12397,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12397,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12397,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12397,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12397,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12397,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12397,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12397,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12397,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12397,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12397,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12397,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12397,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12397,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12397,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12397,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12397,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12397,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12397,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12397,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12397,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12397,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12397,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12397,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12397,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12397,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12397,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12397,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12397,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12397,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12397,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12397,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12397,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12397,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12397,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12397,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12397,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12397,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12397,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12397,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12397,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12397,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12397,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12397,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12397,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12397,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12397,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12397,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12397,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12397,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12397,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12397,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12397,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12397,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12397,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12397,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12397,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12397,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12397,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12397,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12397,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12397,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12397,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12397,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12397,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12397,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12397,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12397,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12397,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12397,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12397,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12397,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12397,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12397,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12397,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12397 : FrameRepair 12397 scalarRow12397 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12397Cells j).1 (repair12397Cells j).2.1
  endpoint_upper := fun j => ((repair12397Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12397Cells j).2.2

theorem repair12398Cells (j : Fin 43) :
    0 ≤ (scalarRow12398.table (sourceIndex j)).upper ∧
    (scalarRow12398.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12398.table (sourceIndex j)).centre) /
      (scalarRow12398.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12398.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12398,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12398,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12398,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12398,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12398,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12398,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12398,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12398,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12398,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12398,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12398,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12398,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12398,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12398,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12398,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12398,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12398,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12398,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12398,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12398,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12398,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12398,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12398,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12398,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12398,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12398,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12398,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12398,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12398,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12398,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12398,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12398,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12398,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12398,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12398,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12398,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12398,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12398,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12398,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12398,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12398,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12398,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12398,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12398,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12398,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12398,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12398,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12398,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12398,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12398,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12398,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12398,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12398,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12398,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12398,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12398,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12398,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12398,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12398,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12398,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12398,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12398,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12398,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12398,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12398,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12398,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12398,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12398,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12398,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12398,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12398,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12398,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12398,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12398,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12398,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12398,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12398,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12398,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12398,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12398,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12398,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12398,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12398,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12398,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12398,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12398,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12398 : FrameRepair 12398 scalarRow12398 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12398Cells j).1 (repair12398Cells j).2.1
  endpoint_upper := fun j => ((repair12398Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12398Cells j).2.2

theorem repair12399Cells (j : Fin 43) :
    0 ≤ (scalarRow12399.table (sourceIndex j)).upper ∧
    (scalarRow12399.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12399.table (sourceIndex j)).centre) /
      (scalarRow12399.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12399.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12399,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12399,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12399,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12399,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12399,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12399,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12399,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12399,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12399,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12399,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12399,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12399,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12399,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12399,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12399,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12399,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12399,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12399,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12399,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12399,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12399,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12399,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12399,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12399,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12399,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12399,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12399,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12399,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12399,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12399,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12399,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12399,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12399,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12399,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12399,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12399,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12399,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12399,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12399,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12399,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12399,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12399,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12399,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12399,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12399,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12399,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12399,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12399,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12399,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12399,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12399,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12399,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12399,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12399,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12399,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12399,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12399,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12399,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12399,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12399,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12399,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12399,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12399,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12399,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12399,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12399,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12399,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12399,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12399,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12399,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12399,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12399,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12399,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12399,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12399,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12399,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12399,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12399,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12399,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12399,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12399,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12399,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12399,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12399,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12399,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12399,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12399 : FrameRepair 12399 scalarRow12399 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12399Cells j).1 (repair12399Cells j).2.1
  endpoint_upper := fun j => ((repair12399Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12399Cells j).2.2

end BstLean.Part269
