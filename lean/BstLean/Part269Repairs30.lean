import BstLean.Part269Rows30
import BstLean.Part269RepairCommon
namespace BstLean.Part269
open Real Set BstLean.Part255 BstLean.Part263 BstLean.Part264
theorem repair13100Cells (j : Fin 43) :
    0 ≤ (scalarRow13100.table (sourceIndex j)).upper ∧
    (scalarRow13100.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13100.table (sourceIndex j)).centre) /
      (scalarRow13100.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13100.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13100,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13100,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13100,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13100,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13100,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13100,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13100,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13100,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13100,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13100,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13100,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13100,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13100,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13100,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13100,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13100,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13100,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13100,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13100,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13100,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13100,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13100,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13100,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13100,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13100,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13100,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13100,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13100,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13100,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13100,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13100,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13100,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13100,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13100,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13100,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13100,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13100,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13100,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13100,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13100,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13100,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13100,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13100,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13100,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13100,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13100,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13100,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13100,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13100,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13100,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13100,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13100,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13100,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13100,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13100,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13100,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13100,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13100,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13100,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13100,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13100,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13100,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13100,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13100,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13100,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13100,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13100,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13100,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13100,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13100,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13100,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13100,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13100,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13100,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13100,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13100,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13100,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13100,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13100,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13100,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13100,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13100,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13100,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13100,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13100,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13100,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13100 : FrameRepair 13100 scalarRow13100 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13100Cells j).1 (repair13100Cells j).2.1
  endpoint_upper := fun j => ((repair13100Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13100Cells j).2.2

theorem repair13101Cells (j : Fin 43) :
    0 ≤ (scalarRow13101.table (sourceIndex j)).upper ∧
    (scalarRow13101.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13101.table (sourceIndex j)).centre) /
      (scalarRow13101.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13101.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13101,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13101,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13101,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13101,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13101,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13101,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13101,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13101,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13101,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13101,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13101,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13101,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13101,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13101,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13101,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13101,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13101,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13101,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13101,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13101,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13101,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13101,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13101,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13101,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13101,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13101,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13101,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13101,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13101,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13101,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13101,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13101,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13101,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13101,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13101,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13101,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13101,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13101,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13101,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13101,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13101,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13101,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13101,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13101,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13101,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13101,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13101,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13101,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13101,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13101,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13101,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13101,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13101,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13101,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13101,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13101,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13101,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13101,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13101,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13101,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13101,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13101,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13101,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13101,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13101,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13101,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13101,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13101,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13101,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13101,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13101,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13101,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13101,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13101,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13101,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13101,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13101,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13101,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13101,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13101,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13101,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13101,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13101,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13101,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13101,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13101,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13101 : FrameRepair 13101 scalarRow13101 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13101Cells j).1 (repair13101Cells j).2.1
  endpoint_upper := fun j => ((repair13101Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13101Cells j).2.2

theorem repair13102Cells (j : Fin 43) :
    0 ≤ (scalarRow13102.table (sourceIndex j)).upper ∧
    (scalarRow13102.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13102.table (sourceIndex j)).centre) /
      (scalarRow13102.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13102.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13102,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13102,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13102,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13102,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13102,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13102,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13102,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13102,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13102,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13102,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13102,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13102,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13102,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13102,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13102,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13102,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13102,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13102,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13102,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13102,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13102,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13102,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13102,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13102,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13102,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13102,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13102,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13102,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13102,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13102,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13102,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13102,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13102,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13102,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13102,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13102,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13102,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13102,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13102,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13102,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13102,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13102,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13102,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13102,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13102,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13102,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13102,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13102,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13102,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13102,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13102,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13102,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13102,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13102,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13102,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13102,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13102,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13102,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13102,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13102,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13102,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13102,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13102,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13102,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13102,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13102,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13102,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13102,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13102,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13102,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13102,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13102,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13102,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13102,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13102,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13102,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13102,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13102,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13102,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13102,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13102,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13102,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13102,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13102,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13102,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13102,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13102 : FrameRepair 13102 scalarRow13102 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13102Cells j).1 (repair13102Cells j).2.1
  endpoint_upper := fun j => ((repair13102Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13102Cells j).2.2

theorem repair13103Cells (j : Fin 43) :
    0 ≤ (scalarRow13103.table (sourceIndex j)).upper ∧
    (scalarRow13103.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13103.table (sourceIndex j)).centre) /
      (scalarRow13103.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13103.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13103,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13103,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13103,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13103,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13103,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13103,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13103,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13103,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13103,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13103,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13103,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13103,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13103,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13103,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13103,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13103,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13103,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13103,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13103,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13103,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13103,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13103,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13103,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13103,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13103,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13103,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13103,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13103,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13103,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13103,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13103,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13103,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13103,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13103,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13103,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13103,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13103,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13103,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13103,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13103,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13103,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13103,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13103,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13103,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13103,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13103,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13103,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13103,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13103,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13103,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13103,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13103,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13103,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13103,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13103,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13103,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13103,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13103,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13103,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13103,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13103,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13103,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13103,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13103,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13103,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13103,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13103,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13103,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13103,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13103,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13103,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13103,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13103,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13103,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13103,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13103,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13103,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13103,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13103,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13103,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13103,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13103,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13103,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13103,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13103,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13103,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13103 : FrameRepair 13103 scalarRow13103 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13103Cells j).1 (repair13103Cells j).2.1
  endpoint_upper := fun j => ((repair13103Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13103Cells j).2.2

theorem repair13104Cells (j : Fin 43) :
    0 ≤ (scalarRow13104.table (sourceIndex j)).upper ∧
    (scalarRow13104.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13104.table (sourceIndex j)).centre) /
      (scalarRow13104.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13104.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13104,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13104,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13104,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13104,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13104,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13104,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13104,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13104,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13104,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13104,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13104,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13104,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13104,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13104,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13104,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13104,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13104,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13104,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13104,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13104,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13104,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13104,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13104,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13104,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13104,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13104,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13104,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13104,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13104,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13104,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13104,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13104,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13104,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13104,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13104,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13104,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13104,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13104,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13104,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13104,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13104,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13104,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13104,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13104,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13104,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13104,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13104,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13104,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13104,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13104,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13104,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13104,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13104,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13104,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13104,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13104,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13104,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13104,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13104,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13104,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13104,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13104,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13104,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13104,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13104,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13104,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13104,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13104,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13104,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13104,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13104,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13104,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13104,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13104,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13104,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13104,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13104,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13104,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13104,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13104,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13104,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13104,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13104,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13104,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13104,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13104,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13104 : FrameRepair 13104 scalarRow13104 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13104Cells j).1 (repair13104Cells j).2.1
  endpoint_upper := fun j => ((repair13104Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13104Cells j).2.2

theorem repair13105Cells (j : Fin 43) :
    0 ≤ (scalarRow13105.table (sourceIndex j)).upper ∧
    (scalarRow13105.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13105.table (sourceIndex j)).centre) /
      (scalarRow13105.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13105.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13105,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13105,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13105,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13105,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13105,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13105,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13105,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13105,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13105,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13105,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13105,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13105,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13105,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13105,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13105,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13105,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13105,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13105,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13105,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13105,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13105,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13105,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13105,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13105,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13105,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13105,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13105,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13105,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13105,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13105,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13105,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13105,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13105,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13105,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13105,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13105,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13105,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13105,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13105,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13105,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13105,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13105,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13105,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13105,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13105,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13105,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13105,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13105,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13105,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13105,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13105,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13105,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13105,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13105,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13105,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13105,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13105,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13105,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13105,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13105,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13105,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13105,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13105,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13105,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13105,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13105,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13105,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13105,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13105,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13105,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13105,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13105,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13105,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13105,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13105,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13105,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13105,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13105,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13105,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13105,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13105,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13105,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13105,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13105,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13105,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13105,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13105 : FrameRepair 13105 scalarRow13105 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13105Cells j).1 (repair13105Cells j).2.1
  endpoint_upper := fun j => ((repair13105Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13105Cells j).2.2

theorem repair13106Cells (j : Fin 43) :
    0 ≤ (scalarRow13106.table (sourceIndex j)).upper ∧
    (scalarRow13106.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13106.table (sourceIndex j)).centre) /
      (scalarRow13106.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13106.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13106,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13106,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13106,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13106,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13106,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13106,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13106,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13106,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13106,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13106,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13106,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13106,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13106,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13106,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13106,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13106,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13106,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13106,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13106,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13106,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13106,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13106,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13106,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13106,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13106,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13106,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13106,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13106,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13106,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13106,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13106,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13106,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13106,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13106,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13106,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13106,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13106,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13106,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13106,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13106,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13106,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13106,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13106,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13106,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13106,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13106,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13106,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13106,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13106,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13106,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13106,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13106,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13106,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13106,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13106,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13106,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13106,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13106,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13106,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13106,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13106,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13106,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13106,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13106,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13106,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13106,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13106,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13106,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13106,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13106,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13106,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13106,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13106,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13106,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13106,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13106,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13106,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13106,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13106,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13106,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13106,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13106,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13106,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13106,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13106,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13106,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13106 : FrameRepair 13106 scalarRow13106 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13106Cells j).1 (repair13106Cells j).2.1
  endpoint_upper := fun j => ((repair13106Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13106Cells j).2.2

theorem repair13107Cells (j : Fin 43) :
    0 ≤ (scalarRow13107.table (sourceIndex j)).upper ∧
    (scalarRow13107.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13107.table (sourceIndex j)).centre) /
      (scalarRow13107.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13107.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13107,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13107,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13107,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13107,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13107,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13107,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13107,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13107,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13107,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13107,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13107,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13107,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13107,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13107,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13107,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13107,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13107,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13107,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13107,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13107,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13107,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13107,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13107,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13107,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13107,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13107,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13107,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13107,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13107,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13107,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13107,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13107,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13107,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13107,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13107,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13107,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13107,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13107,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13107,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13107,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13107,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13107,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13107,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13107,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13107,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13107,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13107,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13107,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13107,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13107,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13107,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13107,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13107,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13107,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13107,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13107,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13107,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13107,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13107,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13107,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13107,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13107,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13107,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13107,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13107,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13107,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13107,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13107,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13107,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13107,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13107,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13107,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13107,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13107,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13107,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13107,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13107,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13107,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13107,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13107,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13107,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13107,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13107,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13107,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13107,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13107,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13107 : FrameRepair 13107 scalarRow13107 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13107Cells j).1 (repair13107Cells j).2.1
  endpoint_upper := fun j => ((repair13107Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13107Cells j).2.2

theorem repair13108Cells (j : Fin 43) :
    0 ≤ (scalarRow13108.table (sourceIndex j)).upper ∧
    (scalarRow13108.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13108.table (sourceIndex j)).centre) /
      (scalarRow13108.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13108.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13108,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13108,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13108,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13108,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13108,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13108,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13108,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13108,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13108,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13108,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13108,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13108,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13108,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13108,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13108,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13108,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13108,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13108,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13108,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13108,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13108,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13108,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13108,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13108,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13108,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13108,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13108,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13108,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13108,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13108,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13108,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13108,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13108,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13108,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13108,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13108,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13108,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13108,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13108,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13108,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13108,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13108,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13108,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13108,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13108,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13108,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13108,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13108,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13108,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13108,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13108,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13108,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13108,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13108,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13108,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13108,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13108,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13108,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13108,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13108,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13108,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13108,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13108,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13108,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13108,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13108,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13108,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13108,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13108,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13108,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13108,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13108,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13108,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13108,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13108,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13108,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13108,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13108,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13108,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13108,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13108,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13108,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13108,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13108,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13108,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13108,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13108 : FrameRepair 13108 scalarRow13108 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13108Cells j).1 (repair13108Cells j).2.1
  endpoint_upper := fun j => ((repair13108Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13108Cells j).2.2

theorem repair13109Cells (j : Fin 43) :
    0 ≤ (scalarRow13109.table (sourceIndex j)).upper ∧
    (scalarRow13109.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13109.table (sourceIndex j)).centre) /
      (scalarRow13109.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13109.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13109,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13109,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13109,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13109,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13109,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13109,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13109,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13109,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13109,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13109,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13109,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13109,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13109,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13109,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13109,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13109,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13109,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13109,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13109,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13109,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13109,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13109,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13109,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13109,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13109,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13109,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13109,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13109,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13109,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13109,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13109,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13109,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13109,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13109,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13109,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13109,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13109,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13109,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13109,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13109,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13109,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13109,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13109,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13109,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13109,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13109,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13109,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13109,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13109,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13109,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13109,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13109,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13109,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13109,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13109,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13109,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13109,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13109,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13109,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13109,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13109,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13109,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13109,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13109,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13109,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13109,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13109,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13109,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13109,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13109,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13109,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13109,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13109,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13109,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13109,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13109,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13109,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13109,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13109,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13109,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13109,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13109,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13109,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13109,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13109,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13109,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13109 : FrameRepair 13109 scalarRow13109 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13109Cells j).1 (repair13109Cells j).2.1
  endpoint_upper := fun j => ((repair13109Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13109Cells j).2.2

theorem repair13110Cells (j : Fin 43) :
    0 ≤ (scalarRow13110.table (sourceIndex j)).upper ∧
    (scalarRow13110.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13110.table (sourceIndex j)).centre) /
      (scalarRow13110.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13110.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13110,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13110,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13110,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13110,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13110,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13110,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13110,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13110,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13110,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13110,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13110,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13110,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13110,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13110,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13110,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13110,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13110,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13110,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13110,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13110,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13110,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13110,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13110,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13110,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13110,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13110,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13110,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13110,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13110,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13110,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13110,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13110,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13110,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13110,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13110,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13110,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13110,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13110,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13110,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13110,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13110,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13110,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13110,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13110,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13110,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13110,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13110,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13110,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13110,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13110,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13110,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13110,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13110,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13110,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13110,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13110,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13110,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13110,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13110,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13110,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13110,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13110,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13110,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13110,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13110,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13110,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13110,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13110,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13110,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13110,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13110,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13110,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13110,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13110,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13110,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13110,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13110,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13110,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13110,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13110,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13110,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13110,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13110,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13110,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13110,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13110,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13110 : FrameRepair 13110 scalarRow13110 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13110Cells j).1 (repair13110Cells j).2.1
  endpoint_upper := fun j => ((repair13110Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13110Cells j).2.2

theorem repair13111Cells (j : Fin 43) :
    0 ≤ (scalarRow13111.table (sourceIndex j)).upper ∧
    (scalarRow13111.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13111.table (sourceIndex j)).centre) /
      (scalarRow13111.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13111.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13111,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13111,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13111,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13111,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13111,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13111,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13111,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13111,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13111,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13111,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13111,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13111,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13111,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13111,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13111,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13111,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13111,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13111,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13111,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13111,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13111,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13111,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13111,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13111,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13111,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13111,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13111,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13111,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13111,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13111,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13111,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13111,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13111,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13111,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13111,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13111,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13111,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13111,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13111,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13111,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13111,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13111,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13111,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13111,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13111,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13111,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13111,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13111,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13111,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13111,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13111,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13111,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13111,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13111,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13111,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13111,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13111,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13111,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13111,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13111,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13111,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13111,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13111,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13111,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13111,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13111,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13111,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13111,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13111,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13111,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13111,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13111,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13111,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13111,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13111,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13111,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13111,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13111,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13111,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13111,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13111,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13111,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13111,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13111,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13111,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13111,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13111 : FrameRepair 13111 scalarRow13111 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13111Cells j).1 (repair13111Cells j).2.1
  endpoint_upper := fun j => ((repair13111Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13111Cells j).2.2

theorem repair13112Cells (j : Fin 43) :
    0 ≤ (scalarRow13112.table (sourceIndex j)).upper ∧
    (scalarRow13112.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13112.table (sourceIndex j)).centre) /
      (scalarRow13112.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13112.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13112,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13112,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13112,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13112,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13112,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13112,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13112,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13112,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13112,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13112,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13112,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13112,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13112,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13112,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13112,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13112,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13112,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13112,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13112,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13112,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13112,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13112,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13112,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13112,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13112,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13112,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13112,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13112,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13112,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13112,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13112,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13112,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13112,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13112,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13112,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13112,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13112,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13112,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13112,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13112,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13112,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13112,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13112,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13112,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13112,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13112,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13112,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13112,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13112,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13112,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13112,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13112,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13112,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13112,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13112,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13112,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13112,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13112,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13112,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13112,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13112,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13112,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13112,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13112,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13112,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13112,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13112,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13112,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13112,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13112,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13112,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13112,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13112,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13112,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13112,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13112,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13112,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13112,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13112,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13112,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13112,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13112,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13112,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13112,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13112,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13112,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13112 : FrameRepair 13112 scalarRow13112 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13112Cells j).1 (repair13112Cells j).2.1
  endpoint_upper := fun j => ((repair13112Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13112Cells j).2.2

theorem repair13113Cells (j : Fin 43) :
    0 ≤ (scalarRow13113.table (sourceIndex j)).upper ∧
    (scalarRow13113.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13113.table (sourceIndex j)).centre) /
      (scalarRow13113.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13113.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13113,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13113,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13113,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13113,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13113,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13113,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13113,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13113,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13113,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13113,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13113,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13113,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13113,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13113,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13113,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13113,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13113,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13113,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13113,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13113,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13113,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13113,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13113,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13113,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13113,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13113,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13113,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13113,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13113,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13113,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13113,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13113,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13113,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13113,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13113,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13113,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13113,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13113,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13113,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13113,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13113,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13113,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13113,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13113,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13113,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13113,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13113,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13113,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13113,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13113,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13113,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13113,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13113,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13113,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13113,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13113,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13113,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13113,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13113,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13113,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13113,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13113,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13113,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13113,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13113,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13113,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13113,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13113,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13113,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13113,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13113,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13113,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13113,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13113,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13113,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13113,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13113,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13113,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13113,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13113,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13113,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13113,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13113,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13113,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13113,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13113,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13113 : FrameRepair 13113 scalarRow13113 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13113Cells j).1 (repair13113Cells j).2.1
  endpoint_upper := fun j => ((repair13113Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13113Cells j).2.2

theorem repair13114Cells (j : Fin 43) :
    0 ≤ (scalarRow13114.table (sourceIndex j)).upper ∧
    (scalarRow13114.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13114.table (sourceIndex j)).centre) /
      (scalarRow13114.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13114.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13114,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13114,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13114,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13114,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13114,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13114,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13114,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13114,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13114,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13114,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13114,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13114,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13114,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13114,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13114,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13114,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13114,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13114,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13114,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13114,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13114,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13114,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13114,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13114,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13114,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13114,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13114,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13114,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13114,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13114,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13114,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13114,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13114,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13114,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13114,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13114,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13114,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13114,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13114,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13114,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13114,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13114,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13114,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13114,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13114,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13114,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13114,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13114,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13114,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13114,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13114,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13114,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13114,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13114,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13114,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13114,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13114,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13114,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13114,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13114,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13114,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13114,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13114,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13114,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13114,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13114,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13114,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13114,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13114,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13114,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13114,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13114,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13114,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13114,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13114,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13114,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13114,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13114,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13114,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13114,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13114,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13114,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13114,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13114,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13114,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13114,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13114 : FrameRepair 13114 scalarRow13114 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13114Cells j).1 (repair13114Cells j).2.1
  endpoint_upper := fun j => ((repair13114Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13114Cells j).2.2

theorem repair13115Cells (j : Fin 43) :
    0 ≤ (scalarRow13115.table (sourceIndex j)).upper ∧
    (scalarRow13115.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13115.table (sourceIndex j)).centre) /
      (scalarRow13115.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13115.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13115,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13115,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13115,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13115,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13115,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13115,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13115,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13115,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13115,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13115,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13115,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13115,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13115,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13115,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13115,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13115,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13115,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13115,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13115,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13115,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13115,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13115,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13115,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13115,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13115,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13115,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13115,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13115,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13115,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13115,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13115,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13115,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13115,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13115,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13115,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13115,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13115,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13115,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13115,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13115,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13115,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13115,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13115,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13115,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13115,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13115,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13115,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13115,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13115,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13115,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13115,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13115,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13115,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13115,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13115,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13115,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13115,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13115,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13115,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13115,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13115,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13115,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13115,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13115,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13115,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13115,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13115,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13115,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13115,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13115,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13115,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13115,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13115,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13115,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13115,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13115,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13115,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13115,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13115,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13115,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13115,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13115,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13115,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13115,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13115,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13115,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13115 : FrameRepair 13115 scalarRow13115 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13115Cells j).1 (repair13115Cells j).2.1
  endpoint_upper := fun j => ((repair13115Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13115Cells j).2.2

theorem repair13116Cells (j : Fin 43) :
    0 ≤ (scalarRow13116.table (sourceIndex j)).upper ∧
    (scalarRow13116.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13116.table (sourceIndex j)).centre) /
      (scalarRow13116.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13116.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13116,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13116,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13116,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13116,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13116,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13116,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13116,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13116,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13116,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13116,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13116,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13116,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13116,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13116,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13116,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13116,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13116,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13116,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13116,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13116,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13116,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13116,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13116,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13116,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13116,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13116,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13116,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13116,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13116,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13116,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13116,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13116,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13116,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13116,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13116,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13116,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13116,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13116,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13116,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13116,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13116,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13116,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13116,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13116,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13116,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13116,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13116,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13116,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13116,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13116,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13116,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13116,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13116,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13116,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13116,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13116,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13116,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13116,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13116,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13116,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13116,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13116,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13116,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13116,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13116,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13116,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13116,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13116,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13116,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13116,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13116,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13116,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13116,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13116,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13116,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13116,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13116,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13116,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13116,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13116,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13116,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13116,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13116,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13116,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13116,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13116,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13116 : FrameRepair 13116 scalarRow13116 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13116Cells j).1 (repair13116Cells j).2.1
  endpoint_upper := fun j => ((repair13116Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13116Cells j).2.2

theorem repair13117Cells (j : Fin 43) :
    0 ≤ (scalarRow13117.table (sourceIndex j)).upper ∧
    (scalarRow13117.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13117.table (sourceIndex j)).centre) /
      (scalarRow13117.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13117.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13117,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13117,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13117,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13117,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13117,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13117,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13117,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13117,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13117,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13117,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13117,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13117,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13117,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13117,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13117,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13117,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13117,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13117,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13117,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13117,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13117,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13117,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13117,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13117,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13117,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13117,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13117,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13117,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13117,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13117,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13117,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13117,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13117,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13117,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13117,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13117,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13117,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13117,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13117,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13117,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13117,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13117,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13117,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13117,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13117,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13117,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13117,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13117,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13117,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13117,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13117,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13117,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13117,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13117,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13117,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13117,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13117,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13117,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13117,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13117,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13117,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13117,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13117,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13117,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13117,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13117,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13117,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13117,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13117,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13117,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13117,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13117,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13117,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13117,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13117,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13117,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13117,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13117,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13117,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13117,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13117,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13117,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13117,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13117,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13117,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13117,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13117 : FrameRepair 13117 scalarRow13117 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13117Cells j).1 (repair13117Cells j).2.1
  endpoint_upper := fun j => ((repair13117Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13117Cells j).2.2

theorem repair13118Cells (j : Fin 43) :
    0 ≤ (scalarRow13118.table (sourceIndex j)).upper ∧
    (scalarRow13118.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13118.table (sourceIndex j)).centre) /
      (scalarRow13118.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13118.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13118,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13118,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13118,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13118,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13118,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13118,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13118,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13118,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13118,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13118,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13118,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13118,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13118,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13118,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13118,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13118,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13118,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13118,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13118,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13118,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13118,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13118,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13118,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13118,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13118,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13118,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13118,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13118,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13118,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13118,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13118,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13118,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13118,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13118,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13118,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13118,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13118,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13118,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13118,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13118,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13118,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13118,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13118,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13118,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13118,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13118,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13118,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13118,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13118,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13118,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13118,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13118,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13118,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13118,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13118,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13118,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13118,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13118,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13118,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13118,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13118,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13118,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13118,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13118,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13118,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13118,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13118,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13118,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13118,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13118,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13118,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13118,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13118,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13118,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13118,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13118,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13118,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13118,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13118,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13118,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13118,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13118,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13118,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13118,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13118,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13118,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13118 : FrameRepair 13118 scalarRow13118 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13118Cells j).1 (repair13118Cells j).2.1
  endpoint_upper := fun j => ((repair13118Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13118Cells j).2.2

theorem repair13119Cells (j : Fin 43) :
    0 ≤ (scalarRow13119.table (sourceIndex j)).upper ∧
    (scalarRow13119.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13119.table (sourceIndex j)).centre) /
      (scalarRow13119.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13119.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13119,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13119,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13119,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13119,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13119,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13119,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13119,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13119,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13119,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13119,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13119,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13119,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13119,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13119,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13119,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13119,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13119,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13119,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13119,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13119,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13119,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13119,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13119,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13119,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13119,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13119,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13119,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13119,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13119,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13119,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13119,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13119,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13119,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13119,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13119,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13119,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13119,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13119,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13119,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13119,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13119,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13119,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13119,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13119,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13119,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13119,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13119,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13119,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13119,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13119,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13119,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13119,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13119,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13119,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13119,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13119,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13119,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13119,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13119,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13119,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13119,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13119,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13119,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13119,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13119,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13119,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13119,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13119,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13119,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13119,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13119,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13119,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13119,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13119,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13119,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13119,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13119,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13119,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13119,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13119,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13119,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13119,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13119,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13119,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13119,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13119,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13119 : FrameRepair 13119 scalarRow13119 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13119Cells j).1 (repair13119Cells j).2.1
  endpoint_upper := fun j => ((repair13119Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13119Cells j).2.2

theorem repair13120Cells (j : Fin 43) :
    0 ≤ (scalarRow13120.table (sourceIndex j)).upper ∧
    (scalarRow13120.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13120.table (sourceIndex j)).centre) /
      (scalarRow13120.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13120.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13120,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13120,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13120,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13120,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13120,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13120,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13120,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13120,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13120,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13120,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13120,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13120,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13120,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13120,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13120,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13120,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13120,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13120,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13120,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13120,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13120,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13120,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13120,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13120,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13120,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13120,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13120,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13120,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13120,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13120,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13120,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13120,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13120,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13120,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13120,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13120,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13120,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13120,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13120,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13120,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13120,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13120,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13120,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13120,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13120,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13120,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13120,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13120,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13120,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13120,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13120,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13120,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13120,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13120,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13120,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13120,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13120,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13120,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13120,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13120,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13120,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13120,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13120,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13120,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13120,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13120,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13120,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13120,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13120,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13120,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13120,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13120,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13120,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13120,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13120,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13120,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13120,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13120,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13120,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13120,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13120,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13120,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13120,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13120,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13120,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13120,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13120 : FrameRepair 13120 scalarRow13120 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13120Cells j).1 (repair13120Cells j).2.1
  endpoint_upper := fun j => ((repair13120Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13120Cells j).2.2

theorem repair13121Cells (j : Fin 43) :
    0 ≤ (scalarRow13121.table (sourceIndex j)).upper ∧
    (scalarRow13121.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13121.table (sourceIndex j)).centre) /
      (scalarRow13121.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13121.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13121,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13121,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13121,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13121,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13121,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13121,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13121,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13121,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13121,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13121,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13121,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13121,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13121,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13121,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13121,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13121,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13121,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13121,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13121,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13121,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13121,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13121,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13121,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13121,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13121,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13121,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13121,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13121,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13121,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13121,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13121,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13121,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13121,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13121,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13121,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13121,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13121,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13121,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13121,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13121,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13121,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13121,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13121,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13121,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13121,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13121,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13121,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13121,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13121,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13121,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13121,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13121,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13121,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13121,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13121,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13121,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13121,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13121,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13121,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13121,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13121,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13121,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13121,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13121,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13121,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13121,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13121,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13121,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13121,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13121,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13121,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13121,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13121,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13121,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13121,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13121,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13121,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13121,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13121,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13121,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13121,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13121,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13121,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13121,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13121,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13121,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13121 : FrameRepair 13121 scalarRow13121 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13121Cells j).1 (repair13121Cells j).2.1
  endpoint_upper := fun j => ((repair13121Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13121Cells j).2.2

theorem repair13122Cells (j : Fin 43) :
    0 ≤ (scalarRow13122.table (sourceIndex j)).upper ∧
    (scalarRow13122.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13122.table (sourceIndex j)).centre) /
      (scalarRow13122.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13122.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13122,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13122,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13122,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13122,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13122,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13122,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13122,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13122,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13122,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13122,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13122,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13122,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13122,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13122,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13122,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13122,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13122,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13122,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13122,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13122,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13122,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13122,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13122,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13122,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13122,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13122,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13122,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13122,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13122,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13122,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13122,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13122,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13122,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13122,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13122,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13122,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13122,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13122,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13122,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13122,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13122,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13122,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13122,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13122,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13122,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13122,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13122,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13122,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13122,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13122,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13122,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13122,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13122,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13122,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13122,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13122,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13122,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13122,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13122,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13122,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13122,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13122,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13122,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13122,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13122,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13122,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13122,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13122,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13122,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13122,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13122,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13122,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13122,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13122,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13122,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13122,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13122,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13122,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13122,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13122,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13122,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13122,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13122,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13122,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13122,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13122,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13122 : FrameRepair 13122 scalarRow13122 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13122Cells j).1 (repair13122Cells j).2.1
  endpoint_upper := fun j => ((repair13122Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13122Cells j).2.2

theorem repair13123Cells (j : Fin 43) :
    0 ≤ (scalarRow13123.table (sourceIndex j)).upper ∧
    (scalarRow13123.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13123.table (sourceIndex j)).centre) /
      (scalarRow13123.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13123.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13123,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13123,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13123,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13123,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13123,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13123,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13123,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13123,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13123,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13123,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13123,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13123,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13123,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13123,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13123,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13123,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13123,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13123,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13123,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13123,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13123,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13123,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13123,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13123,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13123,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13123,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13123,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13123,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13123,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13123,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13123,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13123,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13123,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13123,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13123,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13123,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13123,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13123,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13123,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13123,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13123,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13123,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13123,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13123,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13123,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13123,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13123,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13123,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13123,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13123,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13123,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13123,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13123,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13123,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13123,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13123,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13123,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13123,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13123,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13123,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13123,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13123,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13123,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13123,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13123,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13123,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13123,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13123,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13123,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13123,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13123,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13123,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13123,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13123,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13123,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13123,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13123,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13123,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13123,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13123,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13123,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13123,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13123,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13123,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13123,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13123,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13123 : FrameRepair 13123 scalarRow13123 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13123Cells j).1 (repair13123Cells j).2.1
  endpoint_upper := fun j => ((repair13123Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13123Cells j).2.2

theorem repair13124Cells (j : Fin 43) :
    0 ≤ (scalarRow13124.table (sourceIndex j)).upper ∧
    (scalarRow13124.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13124.table (sourceIndex j)).centre) /
      (scalarRow13124.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13124.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13124,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13124,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13124,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13124,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13124,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13124,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13124,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13124,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13124,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13124,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13124,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13124,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13124,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13124,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13124,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13124,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13124,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13124,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13124,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13124,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13124,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13124,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13124,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13124,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13124,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13124,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13124,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13124,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13124,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13124,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13124,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13124,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13124,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13124,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13124,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13124,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13124,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13124,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13124,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13124,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13124,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13124,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13124,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13124,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13124,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13124,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13124,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13124,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13124,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13124,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13124,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13124,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13124,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13124,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13124,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13124,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13124,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13124,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13124,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13124,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13124,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13124,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13124,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13124,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13124,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13124,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13124,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13124,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13124,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13124,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13124,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13124,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13124,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13124,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13124,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13124,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13124,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13124,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13124,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13124,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13124,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13124,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13124,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13124,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13124,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13124,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13124 : FrameRepair 13124 scalarRow13124 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13124Cells j).1 (repair13124Cells j).2.1
  endpoint_upper := fun j => ((repair13124Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13124Cells j).2.2

end BstLean.Part269
