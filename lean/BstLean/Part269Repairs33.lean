import BstLean.Part269Rows33
import BstLean.Part269RepairCommon
namespace BstLean.Part269
open Real Set BstLean.Part255 BstLean.Part263 BstLean.Part264
theorem repair13175Cells (j : Fin 43) :
    0 ≤ (scalarRow13175.table (sourceIndex j)).upper ∧
    (scalarRow13175.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13175.table (sourceIndex j)).centre) /
      (scalarRow13175.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13175.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13175,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13175,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13175,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13175,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13175,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13175,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13175,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13175,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13175,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13175,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13175,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13175,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13175,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13175,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13175,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13175,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13175,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13175,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13175,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13175,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13175,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13175,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13175,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13175,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13175,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13175,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13175,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13175,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13175,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13175,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13175,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13175,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13175,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13175,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13175,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13175,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13175,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13175,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13175,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13175,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13175,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13175,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13175,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13175,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13175,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13175,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13175,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13175,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13175,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13175,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13175,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13175,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13175,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13175,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13175,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13175,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13175,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13175,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13175,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13175,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13175,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13175,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13175,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13175,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13175,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13175,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13175,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13175,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13175,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13175,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13175,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13175,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13175,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13175,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13175,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13175,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13175,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13175,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13175,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13175,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13175,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13175,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13175,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13175,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13175,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13175,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13175 : FrameRepair 13175 scalarRow13175 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13175Cells j).1 (repair13175Cells j).2.1
  endpoint_upper := fun j => ((repair13175Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13175Cells j).2.2

theorem repair13176Cells (j : Fin 43) :
    0 ≤ (scalarRow13176.table (sourceIndex j)).upper ∧
    (scalarRow13176.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13176.table (sourceIndex j)).centre) /
      (scalarRow13176.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13176.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13176,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13176,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13176,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13176,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13176,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13176,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13176,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13176,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13176,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13176,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13176,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13176,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13176,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13176,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13176,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13176,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13176,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13176,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13176,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13176,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13176,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13176,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13176,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13176,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13176,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13176,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13176,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13176,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13176,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13176,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13176,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13176,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13176,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13176,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13176,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13176,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13176,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13176,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13176,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13176,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13176,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13176,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13176,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13176,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13176,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13176,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13176,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13176,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13176,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13176,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13176,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13176,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13176,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13176,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13176,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13176,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13176,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13176,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13176,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13176,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13176,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13176,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13176,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13176,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13176,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13176,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13176,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13176,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13176,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13176,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13176,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13176,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13176,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13176,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13176,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13176,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13176,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13176,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13176,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13176,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13176,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13176,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13176,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13176,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13176,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13176,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13176 : FrameRepair 13176 scalarRow13176 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13176Cells j).1 (repair13176Cells j).2.1
  endpoint_upper := fun j => ((repair13176Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13176Cells j).2.2

theorem repair13177Cells (j : Fin 43) :
    0 ≤ (scalarRow13177.table (sourceIndex j)).upper ∧
    (scalarRow13177.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13177.table (sourceIndex j)).centre) /
      (scalarRow13177.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13177.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13177,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13177,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13177,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13177,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13177,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13177,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13177,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13177,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13177,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13177,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13177,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13177,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13177,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13177,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13177,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13177,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13177,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13177,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13177,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13177,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13177,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13177,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13177,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13177,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13177,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13177,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13177,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13177,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13177,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13177,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13177,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13177,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13177,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13177,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13177,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13177,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13177,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13177,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13177,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13177,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13177,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13177,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13177,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13177,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13177,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13177,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13177,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13177,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13177,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13177,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13177,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13177,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13177,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13177,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13177,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13177,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13177,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13177,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13177,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13177,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13177,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13177,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13177,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13177,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13177,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13177,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13177,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13177,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13177,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13177,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13177,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13177,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13177,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13177,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13177,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13177,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13177,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13177,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13177,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13177,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13177,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13177,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13177,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13177,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13177,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13177,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13177 : FrameRepair 13177 scalarRow13177 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13177Cells j).1 (repair13177Cells j).2.1
  endpoint_upper := fun j => ((repair13177Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13177Cells j).2.2

theorem repair13178Cells (j : Fin 43) :
    0 ≤ (scalarRow13178.table (sourceIndex j)).upper ∧
    (scalarRow13178.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13178.table (sourceIndex j)).centre) /
      (scalarRow13178.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13178.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13178,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13178,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13178,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13178,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13178,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13178,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13178,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13178,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13178,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13178,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13178,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13178,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13178,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13178,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13178,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13178,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13178,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13178,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13178,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13178,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13178,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13178,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13178,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13178,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13178,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13178,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13178,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13178,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13178,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13178,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13178,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13178,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13178,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13178,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13178,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13178,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13178,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13178,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13178,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13178,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13178,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13178,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13178,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13178,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13178,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13178,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13178,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13178,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13178,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13178,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13178,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13178,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13178,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13178,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13178,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13178,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13178,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13178,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13178,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13178,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13178,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13178,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13178,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13178,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13178,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13178,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13178,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13178,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13178,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13178,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13178,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13178,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13178,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13178,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13178,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13178,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13178,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13178,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13178,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13178,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13178,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13178,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13178,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13178,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13178,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13178,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13178 : FrameRepair 13178 scalarRow13178 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13178Cells j).1 (repair13178Cells j).2.1
  endpoint_upper := fun j => ((repair13178Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13178Cells j).2.2

theorem repair13179Cells (j : Fin 43) :
    0 ≤ (scalarRow13179.table (sourceIndex j)).upper ∧
    (scalarRow13179.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13179.table (sourceIndex j)).centre) /
      (scalarRow13179.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13179.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13179,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13179,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13179,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13179,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13179,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13179,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13179,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13179,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13179,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13179,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13179,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13179,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13179,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13179,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13179,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13179,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13179,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13179,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13179,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13179,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13179,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13179,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13179,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13179,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13179,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13179,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13179,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13179,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13179,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13179,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13179,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13179,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13179,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13179,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13179,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13179,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13179,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13179,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13179,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13179,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13179,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13179,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13179,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13179,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13179,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13179,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13179,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13179,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13179,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13179,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13179,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13179,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13179,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13179,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13179,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13179,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13179,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13179,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13179,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13179,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13179,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13179,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13179,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13179,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13179,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13179,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13179,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13179,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13179,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13179,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13179,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13179,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13179,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13179,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13179,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13179,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13179,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13179,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13179,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13179,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13179,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13179,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13179,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13179,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13179,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13179,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13179 : FrameRepair 13179 scalarRow13179 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13179Cells j).1 (repair13179Cells j).2.1
  endpoint_upper := fun j => ((repair13179Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13179Cells j).2.2

theorem repair13180Cells (j : Fin 43) :
    0 ≤ (scalarRow13180.table (sourceIndex j)).upper ∧
    (scalarRow13180.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13180.table (sourceIndex j)).centre) /
      (scalarRow13180.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13180.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13180,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13180,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13180,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13180,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13180,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13180,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13180,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13180,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13180,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13180,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13180,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13180,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13180,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13180,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13180,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13180,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13180,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13180,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13180,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13180,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13180,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13180,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13180,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13180,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13180,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13180,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13180,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13180,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13180,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13180,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13180,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13180,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13180,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13180,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13180,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13180,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13180,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13180,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13180,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13180,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13180,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13180,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13180,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13180,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13180,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13180,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13180,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13180,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13180,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13180,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13180,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13180,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13180,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13180,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13180,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13180,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13180,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13180,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13180,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13180,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13180,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13180,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13180,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13180,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13180,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13180,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13180,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13180,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13180,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13180,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13180,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13180,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13180,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13180,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13180,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13180,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13180,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13180,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13180,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13180,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13180,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13180,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13180,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13180,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13180,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13180,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13180 : FrameRepair 13180 scalarRow13180 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13180Cells j).1 (repair13180Cells j).2.1
  endpoint_upper := fun j => ((repair13180Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13180Cells j).2.2

theorem repair13181Cells (j : Fin 43) :
    0 ≤ (scalarRow13181.table (sourceIndex j)).upper ∧
    (scalarRow13181.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13181.table (sourceIndex j)).centre) /
      (scalarRow13181.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13181.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13181,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13181,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13181,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13181,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13181,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13181,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13181,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13181,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13181,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13181,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13181,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13181,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13181,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13181,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13181,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13181,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13181,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13181,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13181,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13181,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13181,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13181,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13181,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13181,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13181,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13181,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13181,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13181,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13181,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13181,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13181,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13181,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13181,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13181,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13181,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13181,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13181,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13181,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13181,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13181,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13181,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13181,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13181,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13181,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13181,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13181,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13181,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13181,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13181,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13181,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13181,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13181,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13181,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13181,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13181,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13181,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13181,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13181,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13181,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13181,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13181,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13181,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13181,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13181,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13181,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13181,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13181,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13181,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13181,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13181,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13181,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13181,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13181,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13181,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13181,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13181,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13181,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13181,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13181,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13181,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13181,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13181,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13181,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13181,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13181,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13181,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13181 : FrameRepair 13181 scalarRow13181 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13181Cells j).1 (repair13181Cells j).2.1
  endpoint_upper := fun j => ((repair13181Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13181Cells j).2.2

theorem repair13182Cells (j : Fin 43) :
    0 ≤ (scalarRow13182.table (sourceIndex j)).upper ∧
    (scalarRow13182.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13182.table (sourceIndex j)).centre) /
      (scalarRow13182.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13182.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13182,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13182,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13182,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13182,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13182,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13182,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13182,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13182,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13182,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13182,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13182,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13182,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13182,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13182,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13182,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13182,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13182,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13182,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13182,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13182,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13182,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13182,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13182,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13182,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13182,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13182,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13182,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13182,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13182,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13182,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13182,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13182,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13182,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13182,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13182,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13182,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13182,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13182,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13182,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13182,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13182,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13182,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13182,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13182,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13182,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13182,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13182,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13182,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13182,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13182,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13182,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13182,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13182,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13182,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13182,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13182,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13182,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13182,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13182,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13182,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13182,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13182,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13182,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13182,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13182,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13182,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13182,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13182,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13182,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13182,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13182,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13182,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13182,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13182,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13182,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13182,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13182,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13182,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13182,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13182,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13182,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13182,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13182,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13182,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13182,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13182,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13182 : FrameRepair 13182 scalarRow13182 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13182Cells j).1 (repair13182Cells j).2.1
  endpoint_upper := fun j => ((repair13182Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13182Cells j).2.2

theorem repair13183Cells (j : Fin 43) :
    0 ≤ (scalarRow13183.table (sourceIndex j)).upper ∧
    (scalarRow13183.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13183.table (sourceIndex j)).centre) /
      (scalarRow13183.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13183.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13183,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13183,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13183,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13183,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13183,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13183,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13183,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13183,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13183,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13183,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13183,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13183,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13183,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13183,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13183,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13183,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13183,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13183,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13183,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13183,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13183,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13183,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13183,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13183,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13183,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13183,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13183,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13183,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13183,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13183,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13183,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13183,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13183,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13183,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13183,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13183,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13183,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13183,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13183,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13183,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13183,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13183,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13183,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13183,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13183,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13183,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13183,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13183,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13183,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13183,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13183,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13183,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13183,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13183,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13183,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13183,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13183,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13183,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13183,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13183,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13183,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13183,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13183,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13183,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13183,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13183,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13183,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13183,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13183,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13183,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13183,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13183,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13183,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13183,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13183,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13183,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13183,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13183,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13183,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13183,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13183,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13183,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13183,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13183,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13183,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13183,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13183 : FrameRepair 13183 scalarRow13183 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13183Cells j).1 (repair13183Cells j).2.1
  endpoint_upper := fun j => ((repair13183Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13183Cells j).2.2

theorem repair13184Cells (j : Fin 43) :
    0 ≤ (scalarRow13184.table (sourceIndex j)).upper ∧
    (scalarRow13184.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13184.table (sourceIndex j)).centre) /
      (scalarRow13184.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13184.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13184,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13184,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13184,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13184,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13184,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13184,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13184,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13184,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13184,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13184,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13184,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13184,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13184,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13184,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13184,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13184,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13184,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13184,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13184,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13184,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13184,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13184,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13184,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13184,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13184,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13184,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13184,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13184,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13184,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13184,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13184,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13184,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13184,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13184,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13184,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13184,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13184,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13184,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13184,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13184,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13184,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13184,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13184,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13184,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13184,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13184,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13184,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13184,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13184,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13184,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13184,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13184,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13184,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13184,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13184,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13184,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13184,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13184,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13184,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13184,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13184,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13184,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13184,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13184,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13184,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13184,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13184,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13184,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13184,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13184,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13184,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13184,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13184,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13184,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13184,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13184,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13184,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13184,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13184,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13184,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13184,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13184,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13184,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13184,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13184,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13184,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13184 : FrameRepair 13184 scalarRow13184 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13184Cells j).1 (repair13184Cells j).2.1
  endpoint_upper := fun j => ((repair13184Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13184Cells j).2.2

theorem repair13185Cells (j : Fin 43) :
    0 ≤ (scalarRow13185.table (sourceIndex j)).upper ∧
    (scalarRow13185.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13185.table (sourceIndex j)).centre) /
      (scalarRow13185.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13185.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13185,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13185,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13185,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13185,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13185,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13185,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13185,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13185,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13185,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13185,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13185,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13185,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13185,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13185,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13185,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13185,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13185,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13185,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13185,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13185,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13185,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13185,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13185,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13185,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13185,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13185,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13185,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13185,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13185,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13185,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13185,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13185,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13185,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13185,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13185,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13185,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13185,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13185,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13185,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13185,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13185,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13185,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13185,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13185,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13185,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13185,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13185,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13185,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13185,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13185,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13185,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13185,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13185,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13185,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13185,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13185,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13185,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13185,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13185,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13185,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13185,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13185,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13185,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13185,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13185,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13185,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13185,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13185,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13185,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13185,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13185,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13185,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13185,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13185,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13185,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13185,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13185,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13185,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13185,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13185,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13185,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13185,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13185,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13185,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13185,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13185,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13185 : FrameRepair 13185 scalarRow13185 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13185Cells j).1 (repair13185Cells j).2.1
  endpoint_upper := fun j => ((repair13185Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13185Cells j).2.2

theorem repair13186Cells (j : Fin 43) :
    0 ≤ (scalarRow13186.table (sourceIndex j)).upper ∧
    (scalarRow13186.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13186.table (sourceIndex j)).centre) /
      (scalarRow13186.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13186.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13186,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13186,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13186,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13186,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13186,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13186,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13186,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13186,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13186,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13186,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13186,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13186,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13186,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13186,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13186,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13186,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13186,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13186,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13186,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13186,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13186,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13186,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13186,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13186,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13186,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13186,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13186,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13186,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13186,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13186,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13186,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13186,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13186,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13186,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13186,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13186,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13186,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13186,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13186,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13186,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13186,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13186,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13186,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13186,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13186,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13186,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13186,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13186,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13186,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13186,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13186,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13186,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13186,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13186,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13186,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13186,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13186,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13186,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13186,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13186,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13186,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13186,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13186,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13186,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13186,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13186,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13186,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13186,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13186,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13186,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13186,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13186,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13186,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13186,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13186,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13186,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13186,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13186,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13186,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13186,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13186,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13186,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13186,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13186,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13186,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13186,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13186 : FrameRepair 13186 scalarRow13186 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13186Cells j).1 (repair13186Cells j).2.1
  endpoint_upper := fun j => ((repair13186Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13186Cells j).2.2

theorem repair13187Cells (j : Fin 43) :
    0 ≤ (scalarRow13187.table (sourceIndex j)).upper ∧
    (scalarRow13187.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13187.table (sourceIndex j)).centre) /
      (scalarRow13187.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13187.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13187,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13187,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13187,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13187,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13187,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13187,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13187,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13187,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13187,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13187,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13187,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13187,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13187,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13187,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13187,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13187,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13187,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13187,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13187,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13187,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13187,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13187,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13187,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13187,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13187,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13187,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13187,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13187,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13187,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13187,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13187,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13187,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13187,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13187,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13187,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13187,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13187,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13187,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13187,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13187,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13187,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13187,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13187,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13187,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13187,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13187,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13187,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13187,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13187,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13187,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13187,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13187,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13187,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13187,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13187,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13187,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13187,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13187,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13187,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13187,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13187,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13187,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13187,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13187,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13187,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13187,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13187,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13187,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13187,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13187,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13187,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13187,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13187,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13187,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13187,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13187,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13187,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13187,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13187,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13187,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13187,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13187,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13187,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13187,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13187,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13187,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13187 : FrameRepair 13187 scalarRow13187 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13187Cells j).1 (repair13187Cells j).2.1
  endpoint_upper := fun j => ((repair13187Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13187Cells j).2.2

theorem repair13188Cells (j : Fin 43) :
    0 ≤ (scalarRow13188.table (sourceIndex j)).upper ∧
    (scalarRow13188.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13188.table (sourceIndex j)).centre) /
      (scalarRow13188.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13188.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13188,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13188,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13188,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13188,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13188,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13188,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13188,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13188,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13188,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13188,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13188,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13188,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13188,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13188,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13188,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13188,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13188,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13188,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13188,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13188,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13188,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13188,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13188,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13188,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13188,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13188,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13188,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13188,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13188,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13188,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13188,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13188,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13188,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13188,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13188,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13188,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13188,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13188,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13188,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13188,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13188,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13188,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13188,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13188,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13188,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13188,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13188,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13188,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13188,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13188,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13188,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13188,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13188,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13188,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13188,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13188,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13188,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13188,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13188,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13188,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13188,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13188,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13188,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13188,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13188,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13188,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13188,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13188,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13188,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13188,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13188,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13188,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13188,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13188,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13188,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13188,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13188,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13188,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13188,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13188,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13188,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13188,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13188,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13188,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13188,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13188,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13188 : FrameRepair 13188 scalarRow13188 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13188Cells j).1 (repair13188Cells j).2.1
  endpoint_upper := fun j => ((repair13188Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13188Cells j).2.2

theorem repair13189Cells (j : Fin 43) :
    0 ≤ (scalarRow13189.table (sourceIndex j)).upper ∧
    (scalarRow13189.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13189.table (sourceIndex j)).centre) /
      (scalarRow13189.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13189.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13189,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13189,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13189,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13189,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13189,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13189,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13189,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13189,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13189,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13189,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13189,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13189,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13189,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13189,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13189,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13189,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13189,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13189,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13189,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13189,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13189,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13189,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13189,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13189,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13189,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13189,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13189,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13189,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13189,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13189,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13189,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13189,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13189,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13189,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13189,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13189,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13189,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13189,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13189,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13189,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13189,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13189,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13189,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13189,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13189,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13189,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13189,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13189,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13189,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13189,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13189,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13189,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13189,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13189,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13189,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13189,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13189,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13189,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13189,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13189,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13189,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13189,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13189,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13189,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13189,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13189,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13189,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13189,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13189,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13189,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13189,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13189,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13189,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13189,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13189,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13189,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13189,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13189,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13189,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13189,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13189,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13189,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13189,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13189,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13189,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13189,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13189 : FrameRepair 13189 scalarRow13189 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13189Cells j).1 (repair13189Cells j).2.1
  endpoint_upper := fun j => ((repair13189Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13189Cells j).2.2

theorem repair13190Cells (j : Fin 43) :
    0 ≤ (scalarRow13190.table (sourceIndex j)).upper ∧
    (scalarRow13190.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13190.table (sourceIndex j)).centre) /
      (scalarRow13190.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13190.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13190,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13190,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13190,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13190,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13190,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13190,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13190,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13190,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13190,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13190,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13190,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13190,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13190,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13190,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13190,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13190,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13190,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13190,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13190,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13190,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13190,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13190,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13190,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13190,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13190,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13190,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13190,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13190,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13190,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13190,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13190,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13190,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13190,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13190,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13190,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13190,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13190,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13190,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13190,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13190,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13190,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13190,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13190,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13190,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13190,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13190,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13190,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13190,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13190,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13190,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13190,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13190,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13190,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13190,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13190,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13190,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13190,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13190,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13190,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13190,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13190,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13190,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13190,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13190,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13190,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13190,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13190,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13190,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13190,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13190,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13190,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13190,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13190,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13190,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13190,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13190,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13190,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13190,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13190,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13190,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13190,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13190,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13190,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13190,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13190,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13190,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13190 : FrameRepair 13190 scalarRow13190 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13190Cells j).1 (repair13190Cells j).2.1
  endpoint_upper := fun j => ((repair13190Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13190Cells j).2.2

theorem repair13191Cells (j : Fin 43) :
    0 ≤ (scalarRow13191.table (sourceIndex j)).upper ∧
    (scalarRow13191.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13191.table (sourceIndex j)).centre) /
      (scalarRow13191.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13191.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13191,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13191,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13191,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13191,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13191,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13191,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13191,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13191,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13191,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13191,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13191,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13191,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13191,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13191,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13191,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13191,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13191,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13191,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13191,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13191,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13191,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13191,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13191,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13191,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13191,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13191,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13191,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13191,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13191,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13191,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13191,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13191,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13191,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13191,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13191,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13191,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13191,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13191,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13191,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13191,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13191,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13191,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13191,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13191,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13191,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13191,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13191,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13191,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13191,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13191,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13191,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13191,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13191,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13191,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13191,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13191,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13191,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13191,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13191,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13191,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13191,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13191,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13191,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13191,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13191,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13191,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13191,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13191,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13191,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13191,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13191,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13191,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13191,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13191,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13191,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13191,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13191,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13191,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13191,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13191,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13191,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13191,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13191,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13191,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13191,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13191,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13191 : FrameRepair 13191 scalarRow13191 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13191Cells j).1 (repair13191Cells j).2.1
  endpoint_upper := fun j => ((repair13191Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13191Cells j).2.2

theorem repair13192Cells (j : Fin 43) :
    0 ≤ (scalarRow13192.table (sourceIndex j)).upper ∧
    (scalarRow13192.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13192.table (sourceIndex j)).centre) /
      (scalarRow13192.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13192.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13192,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13192,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13192,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13192,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13192,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13192,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13192,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13192,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13192,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13192,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13192,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13192,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13192,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13192,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13192,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13192,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13192,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13192,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13192,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13192,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13192,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13192,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13192,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13192,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13192,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13192,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13192,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13192,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13192,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13192,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13192,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13192,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13192,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13192,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13192,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13192,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13192,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13192,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13192,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13192,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13192,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13192,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13192,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13192,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13192,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13192,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13192,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13192,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13192,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13192,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13192,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13192,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13192,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13192,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13192,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13192,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13192,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13192,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13192,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13192,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13192,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13192,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13192,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13192,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13192,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13192,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13192,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13192,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13192,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13192,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13192,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13192,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13192,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13192,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13192,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13192,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13192,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13192,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13192,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13192,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13192,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13192,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13192,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13192,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13192,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13192,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13192 : FrameRepair 13192 scalarRow13192 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13192Cells j).1 (repair13192Cells j).2.1
  endpoint_upper := fun j => ((repair13192Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13192Cells j).2.2

theorem repair13193Cells (j : Fin 43) :
    0 ≤ (scalarRow13193.table (sourceIndex j)).upper ∧
    (scalarRow13193.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13193.table (sourceIndex j)).centre) /
      (scalarRow13193.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13193.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13193,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13193,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13193,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13193,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13193,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13193,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13193,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13193,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13193,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13193,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13193,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13193,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13193,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13193,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13193,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13193,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13193,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13193,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13193,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13193,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13193,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13193,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13193,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13193,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13193,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13193,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13193,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13193,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13193,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13193,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13193,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13193,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13193,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13193,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13193,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13193,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13193,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13193,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13193,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13193,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13193,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13193,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13193,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13193,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13193,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13193,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13193,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13193,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13193,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13193,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13193,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13193,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13193,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13193,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13193,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13193,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13193,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13193,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13193,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13193,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13193,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13193,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13193,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13193,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13193,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13193,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13193,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13193,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13193,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13193,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13193,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13193,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13193,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13193,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13193,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13193,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13193,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13193,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13193,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13193,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13193,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13193,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13193,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13193,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13193,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13193,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13193 : FrameRepair 13193 scalarRow13193 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13193Cells j).1 (repair13193Cells j).2.1
  endpoint_upper := fun j => ((repair13193Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13193Cells j).2.2

theorem repair13194Cells (j : Fin 43) :
    0 ≤ (scalarRow13194.table (sourceIndex j)).upper ∧
    (scalarRow13194.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13194.table (sourceIndex j)).centre) /
      (scalarRow13194.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13194.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13194,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13194,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13194,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13194,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13194,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13194,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13194,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13194,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13194,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13194,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13194,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13194,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13194,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13194,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13194,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13194,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13194,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13194,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13194,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13194,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13194,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13194,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13194,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13194,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13194,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13194,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13194,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13194,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13194,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13194,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13194,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13194,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13194,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13194,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13194,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13194,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13194,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13194,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13194,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13194,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13194,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13194,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13194,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13194,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13194,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13194,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13194,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13194,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13194,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13194,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13194,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13194,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13194,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13194,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13194,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13194,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13194,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13194,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13194,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13194,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13194,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13194,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13194,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13194,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13194,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13194,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13194,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13194,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13194,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13194,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13194,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13194,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13194,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13194,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13194,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13194,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13194,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13194,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13194,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13194,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13194,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13194,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13194,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13194,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13194,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13194,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13194 : FrameRepair 13194 scalarRow13194 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13194Cells j).1 (repair13194Cells j).2.1
  endpoint_upper := fun j => ((repair13194Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13194Cells j).2.2

theorem repair13195Cells (j : Fin 43) :
    0 ≤ (scalarRow13195.table (sourceIndex j)).upper ∧
    (scalarRow13195.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13195.table (sourceIndex j)).centre) /
      (scalarRow13195.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13195.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13195,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13195,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13195,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13195,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13195,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13195,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13195,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13195,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13195,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13195,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13195,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13195,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13195,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13195,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13195,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13195,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13195,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13195,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13195,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13195,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13195,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13195,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13195,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13195,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13195,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13195,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13195,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13195,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13195,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13195,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13195,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13195,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13195,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13195,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13195,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13195,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13195,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13195,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13195,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13195,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13195,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13195,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13195,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13195,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13195,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13195,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13195,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13195,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13195,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13195,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13195,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13195,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13195,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13195,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13195,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13195,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13195,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13195,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13195,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13195,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13195,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13195,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13195,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13195,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13195,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13195,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13195,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13195,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13195,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13195,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13195,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13195,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13195,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13195,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13195,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13195,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13195,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13195,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13195,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13195,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13195,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13195,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13195,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13195,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13195,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13195,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13195 : FrameRepair 13195 scalarRow13195 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13195Cells j).1 (repair13195Cells j).2.1
  endpoint_upper := fun j => ((repair13195Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13195Cells j).2.2

theorem repair13196Cells (j : Fin 43) :
    0 ≤ (scalarRow13196.table (sourceIndex j)).upper ∧
    (scalarRow13196.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13196.table (sourceIndex j)).centre) /
      (scalarRow13196.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13196.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13196,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13196,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13196,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13196,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13196,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13196,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13196,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13196,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13196,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13196,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13196,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13196,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13196,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13196,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13196,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13196,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13196,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13196,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13196,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13196,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13196,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13196,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13196,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13196,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13196,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13196,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13196,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13196,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13196,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13196,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13196,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13196,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13196,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13196,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13196,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13196,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13196,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13196,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13196,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13196,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13196,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13196,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13196,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13196,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13196,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13196,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13196,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13196,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13196,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13196,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13196,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13196,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13196,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13196,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13196,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13196,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13196,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13196,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13196,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13196,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13196,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13196,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13196,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13196,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13196,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13196,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13196,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13196,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13196,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13196,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13196,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13196,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13196,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13196,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13196,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13196,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13196,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13196,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13196,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13196,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13196,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13196,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13196,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13196,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13196,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13196,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13196 : FrameRepair 13196 scalarRow13196 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13196Cells j).1 (repair13196Cells j).2.1
  endpoint_upper := fun j => ((repair13196Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13196Cells j).2.2

theorem repair13197Cells (j : Fin 43) :
    0 ≤ (scalarRow13197.table (sourceIndex j)).upper ∧
    (scalarRow13197.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13197.table (sourceIndex j)).centre) /
      (scalarRow13197.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13197.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13197,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13197,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13197,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13197,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13197,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13197,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13197,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13197,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13197,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13197,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13197,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13197,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13197,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13197,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13197,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13197,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13197,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13197,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13197,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13197,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13197,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13197,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13197,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13197,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13197,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13197,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13197,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13197,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13197,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13197,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13197,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13197,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13197,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13197,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13197,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13197,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13197,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13197,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13197,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13197,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13197,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13197,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13197,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13197,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13197,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13197,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13197,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13197,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13197,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13197,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13197,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13197,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13197,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13197,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13197,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13197,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13197,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13197,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13197,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13197,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13197,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13197,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13197,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13197,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13197,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13197,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13197,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13197,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13197,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13197,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13197,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13197,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13197,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13197,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13197,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13197,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13197,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13197,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13197,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13197,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13197,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13197,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13197,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13197,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13197,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13197,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13197 : FrameRepair 13197 scalarRow13197 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13197Cells j).1 (repair13197Cells j).2.1
  endpoint_upper := fun j => ((repair13197Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13197Cells j).2.2

theorem repair13198Cells (j : Fin 43) :
    0 ≤ (scalarRow13198.table (sourceIndex j)).upper ∧
    (scalarRow13198.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13198.table (sourceIndex j)).centre) /
      (scalarRow13198.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13198.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13198,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13198,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13198,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13198,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13198,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13198,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13198,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13198,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13198,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13198,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13198,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13198,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13198,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13198,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13198,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13198,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13198,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13198,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13198,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13198,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13198,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13198,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13198,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13198,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13198,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13198,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13198,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13198,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13198,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13198,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13198,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13198,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13198,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13198,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13198,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13198,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13198,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13198,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13198,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13198,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13198,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13198,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13198,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13198,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13198,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13198,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13198,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13198,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13198,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13198,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13198,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13198,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13198,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13198,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13198,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13198,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13198,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13198,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13198,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13198,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13198,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13198,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13198,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13198,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13198,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13198,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13198,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13198,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13198,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13198,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13198,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13198,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13198,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13198,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13198,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13198,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13198,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13198,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13198,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13198,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13198,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13198,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13198,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13198,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13198,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13198,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13198 : FrameRepair 13198 scalarRow13198 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13198Cells j).1 (repair13198Cells j).2.1
  endpoint_upper := fun j => ((repair13198Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13198Cells j).2.2

theorem repair13199Cells (j : Fin 43) :
    0 ≤ (scalarRow13199.table (sourceIndex j)).upper ∧
    (scalarRow13199.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13199.table (sourceIndex j)).centre) /
      (scalarRow13199.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13199.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13199,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13199,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13199,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13199,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13199,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13199,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13199,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13199,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13199,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13199,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13199,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13199,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13199,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13199,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13199,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13199,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13199,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13199,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13199,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13199,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13199,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13199,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13199,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13199,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13199,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13199,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13199,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13199,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13199,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13199,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13199,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13199,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13199,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13199,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13199,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13199,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13199,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13199,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13199,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13199,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13199,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13199,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13199,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13199,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13199,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13199,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13199,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13199,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13199,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13199,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13199,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13199,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13199,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13199,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13199,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13199,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13199,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13199,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13199,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13199,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13199,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13199,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13199,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13199,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13199,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13199,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13199,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13199,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13199,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13199,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13199,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13199,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13199,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13199,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13199,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13199,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13199,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13199,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13199,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13199,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13199,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13199,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13199,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13199,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13199,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13199,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13199 : FrameRepair 13199 scalarRow13199 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13199Cells j).1 (repair13199Cells j).2.1
  endpoint_upper := fun j => ((repair13199Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13199Cells j).2.2

end BstLean.Part269
