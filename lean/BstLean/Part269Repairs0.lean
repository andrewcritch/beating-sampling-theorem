import BstLean.Part269Rows0
import BstLean.Part269RepairCommon
namespace BstLean.Part269
open Real Set BstLean.Part255 BstLean.Part263 BstLean.Part264
theorem repair12351Cells (j : Fin 43) :
    0 ≤ (scalarRow12351.table (sourceIndex j)).upper ∧
    (scalarRow12351.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12351.table (sourceIndex j)).centre) /
      (scalarRow12351.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12351.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12351,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12351,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12351,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12351,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12351,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12351,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12351,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12351,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12351,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12351,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12351,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12351,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12351,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12351,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12351,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12351,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12351,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12351,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12351,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12351,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12351,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12351,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12351,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12351,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12351,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12351,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12351,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12351,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12351,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12351,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12351,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12351,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12351,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12351,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12351,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12351,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12351,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12351,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12351,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12351,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12351,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12351,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12351,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12351,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12351,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12351,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12351,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12351,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12351,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12351,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12351,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12351,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12351,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12351,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12351,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12351,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12351,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12351,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12351,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12351,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12351,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12351,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12351,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12351,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12351,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12351,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12351,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12351,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12351,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12351,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12351,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12351,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12351,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12351,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12351,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12351,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12351,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12351,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12351,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12351,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12351,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12351,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12351,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12351,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12351,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12351,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12351 : FrameRepair 12351 scalarRow12351 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12351Cells j).1 (repair12351Cells j).2.1
  endpoint_upper := fun j => ((repair12351Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12351Cells j).2.2

theorem repair12352Cells (j : Fin 43) :
    0 ≤ (scalarRow12352.table (sourceIndex j)).upper ∧
    (scalarRow12352.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12352.table (sourceIndex j)).centre) /
      (scalarRow12352.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12352.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12352,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12352,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12352,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12352,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12352,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12352,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12352,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12352,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12352,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12352,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12352,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12352,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12352,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12352,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12352,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12352,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12352,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12352,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12352,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12352,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12352,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12352,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12352,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12352,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12352,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12352,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12352,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12352,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12352,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12352,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12352,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12352,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12352,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12352,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12352,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12352,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12352,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12352,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12352,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12352,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12352,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12352,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12352,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12352,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12352,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12352,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12352,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12352,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12352,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12352,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12352,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12352,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12352,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12352,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12352,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12352,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12352,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12352,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12352,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12352,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12352,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12352,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12352,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12352,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12352,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12352,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12352,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12352,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12352,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12352,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12352,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12352,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12352,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12352,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12352,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12352,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12352,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12352,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12352,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12352,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12352,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12352,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12352,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12352,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12352,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12352,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12352 : FrameRepair 12352 scalarRow12352 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12352Cells j).1 (repair12352Cells j).2.1
  endpoint_upper := fun j => ((repair12352Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12352Cells j).2.2

theorem repair12353Cells (j : Fin 43) :
    0 ≤ (scalarRow12353.table (sourceIndex j)).upper ∧
    (scalarRow12353.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12353.table (sourceIndex j)).centre) /
      (scalarRow12353.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12353.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12353,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12353,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12353,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12353,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12353,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12353,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12353,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12353,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12353,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12353,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12353,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12353,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12353,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12353,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12353,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12353,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12353,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12353,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12353,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12353,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12353,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12353,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12353,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12353,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12353,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12353,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12353,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12353,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12353,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12353,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12353,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12353,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12353,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12353,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12353,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12353,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12353,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12353,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12353,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12353,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12353,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12353,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12353,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12353,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12353,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12353,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12353,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12353,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12353,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12353,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12353,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12353,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12353,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12353,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12353,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12353,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12353,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12353,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12353,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12353,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12353,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12353,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12353,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12353,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12353,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12353,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12353,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12353,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12353,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12353,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12353,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12353,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12353,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12353,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12353,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12353,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12353,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12353,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12353,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12353,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12353,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12353,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12353,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12353,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12353,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12353,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12353 : FrameRepair 12353 scalarRow12353 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12353Cells j).1 (repair12353Cells j).2.1
  endpoint_upper := fun j => ((repair12353Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12353Cells j).2.2

theorem repair12354Cells (j : Fin 43) :
    0 ≤ (scalarRow12354.table (sourceIndex j)).upper ∧
    (scalarRow12354.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12354.table (sourceIndex j)).centre) /
      (scalarRow12354.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12354.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12354,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12354,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12354,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12354,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12354,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12354,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12354,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12354,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12354,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12354,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12354,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12354,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12354,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12354,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12354,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12354,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12354,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12354,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12354,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12354,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12354,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12354,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12354,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12354,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12354,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12354,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12354,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12354,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12354,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12354,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12354,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12354,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12354,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12354,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12354,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12354,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12354,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12354,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12354,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12354,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12354,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12354,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12354,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12354,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12354,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12354,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12354,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12354,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12354,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12354,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12354,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12354,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12354,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12354,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12354,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12354,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12354,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12354,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12354,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12354,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12354,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12354,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12354,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12354,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12354,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12354,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12354,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12354,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12354,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12354,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12354,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12354,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12354,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12354,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12354,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12354,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12354,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12354,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12354,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12354,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12354,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12354,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12354,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12354,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12354,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12354,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12354 : FrameRepair 12354 scalarRow12354 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12354Cells j).1 (repair12354Cells j).2.1
  endpoint_upper := fun j => ((repair12354Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12354Cells j).2.2

theorem repair12355Cells (j : Fin 43) :
    0 ≤ (scalarRow12355.table (sourceIndex j)).upper ∧
    (scalarRow12355.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12355.table (sourceIndex j)).centre) /
      (scalarRow12355.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12355.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12355,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12355,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12355,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12355,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12355,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12355,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12355,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12355,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12355,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12355,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12355,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12355,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12355,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12355,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12355,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12355,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12355,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12355,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12355,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12355,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12355,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12355,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12355,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12355,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12355,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12355,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12355,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12355,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12355,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12355,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12355,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12355,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12355,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12355,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12355,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12355,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12355,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12355,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12355,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12355,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12355,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12355,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12355,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12355,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12355,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12355,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12355,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12355,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12355,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12355,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12355,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12355,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12355,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12355,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12355,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12355,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12355,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12355,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12355,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12355,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12355,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12355,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12355,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12355,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12355,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12355,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12355,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12355,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12355,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12355,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12355,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12355,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12355,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12355,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12355,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12355,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12355,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12355,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12355,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12355,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12355,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12355,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12355,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12355,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12355,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12355,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12355 : FrameRepair 12355 scalarRow12355 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12355Cells j).1 (repair12355Cells j).2.1
  endpoint_upper := fun j => ((repair12355Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12355Cells j).2.2

theorem repair12356Cells (j : Fin 43) :
    0 ≤ (scalarRow12356.table (sourceIndex j)).upper ∧
    (scalarRow12356.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12356.table (sourceIndex j)).centre) /
      (scalarRow12356.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12356.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12356,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12356,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12356,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12356,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12356,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12356,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12356,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12356,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12356,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12356,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12356,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12356,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12356,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12356,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12356,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12356,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12356,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12356,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12356,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12356,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12356,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12356,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12356,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12356,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12356,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12356,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12356,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12356,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12356,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12356,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12356,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12356,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12356,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12356,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12356,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12356,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12356,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12356,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12356,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12356,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12356,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12356,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12356,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12356,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12356,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12356,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12356,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12356,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12356,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12356,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12356,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12356,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12356,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12356,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12356,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12356,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12356,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12356,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12356,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12356,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12356,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12356,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12356,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12356,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12356,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12356,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12356,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12356,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12356,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12356,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12356,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12356,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12356,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12356,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12356,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12356,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12356,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12356,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12356,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12356,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12356,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12356,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12356,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12356,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12356,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12356,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12356 : FrameRepair 12356 scalarRow12356 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12356Cells j).1 (repair12356Cells j).2.1
  endpoint_upper := fun j => ((repair12356Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12356Cells j).2.2

theorem repair12357Cells (j : Fin 43) :
    0 ≤ (scalarRow12357.table (sourceIndex j)).upper ∧
    (scalarRow12357.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12357.table (sourceIndex j)).centre) /
      (scalarRow12357.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12357.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12357,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12357,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12357,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12357,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12357,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12357,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12357,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12357,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12357,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12357,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12357,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12357,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12357,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12357,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12357,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12357,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12357,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12357,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12357,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12357,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12357,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12357,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12357,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12357,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12357,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12357,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12357,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12357,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12357,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12357,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12357,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12357,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12357,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12357,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12357,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12357,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12357,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12357,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12357,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12357,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12357,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12357,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12357,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12357,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12357,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12357,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12357,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12357,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12357,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12357,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12357,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12357,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12357,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12357,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12357,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12357,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12357,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12357,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12357,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12357,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12357,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12357,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12357,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12357,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12357,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12357,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12357,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12357,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12357,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12357,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12357,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12357,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12357,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12357,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12357,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12357,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12357,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12357,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12357,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12357,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12357,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12357,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12357,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12357,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12357,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12357,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12357 : FrameRepair 12357 scalarRow12357 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12357Cells j).1 (repair12357Cells j).2.1
  endpoint_upper := fun j => ((repair12357Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12357Cells j).2.2

theorem repair12358Cells (j : Fin 43) :
    0 ≤ (scalarRow12358.table (sourceIndex j)).upper ∧
    (scalarRow12358.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12358.table (sourceIndex j)).centre) /
      (scalarRow12358.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12358.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12358,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12358,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12358,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12358,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12358,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12358,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12358,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12358,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12358,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12358,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12358,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12358,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12358,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12358,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12358,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12358,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12358,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12358,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12358,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12358,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12358,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12358,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12358,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12358,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12358,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12358,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12358,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12358,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12358,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12358,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12358,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12358,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12358,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12358,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12358,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12358,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12358,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12358,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12358,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12358,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12358,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12358,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12358,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12358,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12358,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12358,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12358,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12358,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12358,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12358,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12358,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12358,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12358,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12358,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12358,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12358,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12358,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12358,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12358,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12358,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12358,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12358,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12358,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12358,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12358,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12358,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12358,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12358,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12358,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12358,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12358,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12358,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12358,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12358,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12358,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12358,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12358,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12358,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12358,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12358,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12358,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12358,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12358,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12358,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12358,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12358,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12358 : FrameRepair 12358 scalarRow12358 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12358Cells j).1 (repair12358Cells j).2.1
  endpoint_upper := fun j => ((repair12358Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12358Cells j).2.2

theorem repair12359Cells (j : Fin 43) :
    0 ≤ (scalarRow12359.table (sourceIndex j)).upper ∧
    (scalarRow12359.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12359.table (sourceIndex j)).centre) /
      (scalarRow12359.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12359.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12359,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12359,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12359,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12359,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12359,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12359,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12359,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12359,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12359,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12359,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12359,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12359,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12359,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12359,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12359,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12359,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12359,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12359,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12359,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12359,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12359,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12359,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12359,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12359,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12359,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12359,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12359,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12359,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12359,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12359,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12359,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12359,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12359,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12359,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12359,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12359,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12359,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12359,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12359,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12359,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12359,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12359,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12359,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12359,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12359,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12359,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12359,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12359,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12359,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12359,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12359,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12359,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12359,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12359,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12359,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12359,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12359,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12359,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12359,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12359,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12359,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12359,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12359,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12359,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12359,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12359,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12359,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12359,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12359,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12359,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12359,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12359,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12359,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12359,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12359,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12359,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12359,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12359,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12359,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12359,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12359,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12359,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12359,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12359,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12359,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12359,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12359 : FrameRepair 12359 scalarRow12359 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12359Cells j).1 (repair12359Cells j).2.1
  endpoint_upper := fun j => ((repair12359Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12359Cells j).2.2

theorem repair12360Cells (j : Fin 43) :
    0 ≤ (scalarRow12360.table (sourceIndex j)).upper ∧
    (scalarRow12360.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12360.table (sourceIndex j)).centre) /
      (scalarRow12360.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12360.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12360,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12360,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12360,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12360,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12360,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12360,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12360,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12360,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12360,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12360,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12360,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12360,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12360,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12360,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12360,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12360,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12360,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12360,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12360,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12360,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12360,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12360,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12360,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12360,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12360,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12360,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12360,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12360,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12360,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12360,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12360,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12360,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12360,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12360,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12360,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12360,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12360,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12360,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12360,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12360,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12360,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12360,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12360,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12360,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12360,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12360,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12360,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12360,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12360,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12360,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12360,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12360,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12360,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12360,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12360,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12360,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12360,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12360,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12360,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12360,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12360,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12360,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12360,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12360,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12360,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12360,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12360,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12360,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12360,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12360,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12360,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12360,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12360,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12360,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12360,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12360,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12360,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12360,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12360,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12360,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12360,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12360,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12360,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12360,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12360,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12360,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12360 : FrameRepair 12360 scalarRow12360 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12360Cells j).1 (repair12360Cells j).2.1
  endpoint_upper := fun j => ((repair12360Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12360Cells j).2.2

theorem repair12361Cells (j : Fin 43) :
    0 ≤ (scalarRow12361.table (sourceIndex j)).upper ∧
    (scalarRow12361.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12361.table (sourceIndex j)).centre) /
      (scalarRow12361.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12361.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12361,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12361,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12361,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12361,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12361,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12361,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12361,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12361,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12361,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12361,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12361,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12361,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12361,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12361,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12361,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12361,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12361,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12361,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12361,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12361,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12361,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12361,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12361,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12361,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12361,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12361,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12361,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12361,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12361,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12361,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12361,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12361,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12361,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12361,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12361,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12361,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12361,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12361,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12361,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12361,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12361,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12361,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12361,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12361,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12361,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12361,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12361,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12361,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12361,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12361,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12361,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12361,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12361,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12361,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12361,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12361,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12361,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12361,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12361,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12361,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12361,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12361,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12361,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12361,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12361,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12361,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12361,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12361,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12361,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12361,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12361,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12361,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12361,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12361,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12361,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12361,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12361,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12361,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12361,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12361,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12361,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12361,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12361,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12361,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12361,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12361,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12361 : FrameRepair 12361 scalarRow12361 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12361Cells j).1 (repair12361Cells j).2.1
  endpoint_upper := fun j => ((repair12361Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12361Cells j).2.2

theorem repair12362Cells (j : Fin 43) :
    0 ≤ (scalarRow12362.table (sourceIndex j)).upper ∧
    (scalarRow12362.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12362.table (sourceIndex j)).centre) /
      (scalarRow12362.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12362.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12362,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12362,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12362,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12362,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12362,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12362,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12362,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12362,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12362,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12362,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12362,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12362,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12362,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12362,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12362,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12362,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12362,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12362,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12362,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12362,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12362,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12362,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12362,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12362,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12362,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12362,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12362,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12362,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12362,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12362,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12362,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12362,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12362,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12362,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12362,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12362,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12362,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12362,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12362,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12362,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12362,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12362,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12362,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12362,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12362,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12362,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12362,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12362,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12362,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12362,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12362,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12362,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12362,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12362,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12362,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12362,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12362,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12362,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12362,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12362,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12362,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12362,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12362,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12362,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12362,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12362,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12362,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12362,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12362,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12362,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12362,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12362,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12362,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12362,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12362,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12362,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12362,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12362,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12362,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12362,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12362,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12362,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12362,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12362,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12362,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12362,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12362 : FrameRepair 12362 scalarRow12362 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12362Cells j).1 (repair12362Cells j).2.1
  endpoint_upper := fun j => ((repair12362Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12362Cells j).2.2

theorem repair12363Cells (j : Fin 43) :
    0 ≤ (scalarRow12363.table (sourceIndex j)).upper ∧
    (scalarRow12363.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12363.table (sourceIndex j)).centre) /
      (scalarRow12363.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12363.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12363,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12363,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12363,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12363,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12363,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12363,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12363,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12363,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12363,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12363,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12363,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12363,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12363,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12363,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12363,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12363,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12363,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12363,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12363,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12363,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12363,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12363,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12363,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12363,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12363,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12363,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12363,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12363,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12363,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12363,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12363,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12363,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12363,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12363,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12363,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12363,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12363,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12363,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12363,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12363,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12363,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12363,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12363,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12363,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12363,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12363,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12363,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12363,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12363,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12363,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12363,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12363,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12363,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12363,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12363,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12363,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12363,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12363,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12363,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12363,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12363,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12363,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12363,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12363,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12363,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12363,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12363,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12363,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12363,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12363,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12363,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12363,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12363,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12363,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12363,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12363,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12363,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12363,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12363,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12363,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12363,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12363,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12363,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12363,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12363,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12363,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12363 : FrameRepair 12363 scalarRow12363 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12363Cells j).1 (repair12363Cells j).2.1
  endpoint_upper := fun j => ((repair12363Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12363Cells j).2.2

theorem repair12364Cells (j : Fin 43) :
    0 ≤ (scalarRow12364.table (sourceIndex j)).upper ∧
    (scalarRow12364.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12364.table (sourceIndex j)).centre) /
      (scalarRow12364.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12364.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12364,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12364,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12364,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12364,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12364,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12364,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12364,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12364,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12364,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12364,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12364,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12364,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12364,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12364,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12364,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12364,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12364,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12364,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12364,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12364,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12364,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12364,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12364,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12364,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12364,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12364,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12364,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12364,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12364,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12364,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12364,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12364,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12364,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12364,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12364,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12364,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12364,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12364,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12364,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12364,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12364,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12364,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12364,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12364,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12364,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12364,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12364,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12364,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12364,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12364,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12364,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12364,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12364,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12364,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12364,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12364,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12364,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12364,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12364,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12364,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12364,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12364,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12364,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12364,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12364,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12364,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12364,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12364,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12364,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12364,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12364,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12364,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12364,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12364,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12364,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12364,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12364,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12364,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12364,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12364,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12364,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12364,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12364,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12364,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12364,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12364,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12364 : FrameRepair 12364 scalarRow12364 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12364Cells j).1 (repair12364Cells j).2.1
  endpoint_upper := fun j => ((repair12364Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12364Cells j).2.2

theorem repair12365Cells (j : Fin 43) :
    0 ≤ (scalarRow12365.table (sourceIndex j)).upper ∧
    (scalarRow12365.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12365.table (sourceIndex j)).centre) /
      (scalarRow12365.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12365.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12365,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12365,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12365,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12365,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12365,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12365,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12365,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12365,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12365,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12365,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12365,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12365,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12365,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12365,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12365,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12365,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12365,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12365,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12365,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12365,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12365,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12365,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12365,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12365,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12365,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12365,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12365,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12365,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12365,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12365,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12365,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12365,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12365,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12365,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12365,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12365,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12365,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12365,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12365,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12365,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12365,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12365,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12365,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12365,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12365,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12365,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12365,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12365,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12365,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12365,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12365,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12365,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12365,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12365,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12365,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12365,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12365,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12365,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12365,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12365,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12365,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12365,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12365,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12365,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12365,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12365,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12365,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12365,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12365,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12365,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12365,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12365,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12365,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12365,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12365,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12365,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12365,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12365,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12365,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12365,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12365,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12365,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12365,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12365,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12365,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12365,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12365 : FrameRepair 12365 scalarRow12365 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12365Cells j).1 (repair12365Cells j).2.1
  endpoint_upper := fun j => ((repair12365Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12365Cells j).2.2

theorem repair12366Cells (j : Fin 43) :
    0 ≤ (scalarRow12366.table (sourceIndex j)).upper ∧
    (scalarRow12366.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12366.table (sourceIndex j)).centre) /
      (scalarRow12366.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12366.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12366,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12366,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12366,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12366,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12366,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12366,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12366,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12366,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12366,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12366,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12366,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12366,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12366,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12366,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12366,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12366,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12366,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12366,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12366,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12366,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12366,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12366,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12366,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12366,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12366,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12366,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12366,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12366,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12366,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12366,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12366,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12366,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12366,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12366,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12366,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12366,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12366,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12366,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12366,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12366,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12366,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12366,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12366,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12366,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12366,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12366,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12366,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12366,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12366,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12366,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12366,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12366,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12366,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12366,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12366,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12366,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12366,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12366,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12366,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12366,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12366,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12366,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12366,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12366,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12366,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12366,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12366,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12366,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12366,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12366,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12366,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12366,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12366,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12366,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12366,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12366,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12366,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12366,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12366,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12366,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12366,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12366,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12366,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12366,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12366,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12366,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12366 : FrameRepair 12366 scalarRow12366 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12366Cells j).1 (repair12366Cells j).2.1
  endpoint_upper := fun j => ((repair12366Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12366Cells j).2.2

theorem repair12367Cells (j : Fin 43) :
    0 ≤ (scalarRow12367.table (sourceIndex j)).upper ∧
    (scalarRow12367.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12367.table (sourceIndex j)).centre) /
      (scalarRow12367.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12367.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12367,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12367,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12367,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12367,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12367,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12367,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12367,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12367,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12367,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12367,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12367,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12367,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12367,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12367,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12367,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12367,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12367,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12367,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12367,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12367,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12367,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12367,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12367,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12367,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12367,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12367,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12367,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12367,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12367,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12367,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12367,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12367,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12367,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12367,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12367,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12367,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12367,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12367,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12367,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12367,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12367,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12367,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12367,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12367,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12367,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12367,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12367,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12367,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12367,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12367,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12367,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12367,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12367,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12367,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12367,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12367,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12367,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12367,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12367,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12367,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12367,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12367,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12367,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12367,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12367,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12367,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12367,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12367,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12367,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12367,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12367,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12367,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12367,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12367,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12367,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12367,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12367,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12367,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12367,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12367,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12367,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12367,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12367,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12367,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12367,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12367,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12367 : FrameRepair 12367 scalarRow12367 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12367Cells j).1 (repair12367Cells j).2.1
  endpoint_upper := fun j => ((repair12367Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12367Cells j).2.2

theorem repair12368Cells (j : Fin 43) :
    0 ≤ (scalarRow12368.table (sourceIndex j)).upper ∧
    (scalarRow12368.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12368.table (sourceIndex j)).centre) /
      (scalarRow12368.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12368.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12368,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12368,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12368,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12368,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12368,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12368,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12368,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12368,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12368,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12368,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12368,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12368,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12368,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12368,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12368,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12368,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12368,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12368,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12368,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12368,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12368,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12368,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12368,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12368,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12368,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12368,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12368,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12368,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12368,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12368,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12368,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12368,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12368,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12368,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12368,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12368,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12368,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12368,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12368,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12368,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12368,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12368,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12368,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12368,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12368,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12368,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12368,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12368,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12368,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12368,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12368,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12368,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12368,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12368,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12368,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12368,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12368,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12368,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12368,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12368,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12368,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12368,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12368,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12368,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12368,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12368,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12368,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12368,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12368,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12368,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12368,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12368,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12368,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12368,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12368,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12368,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12368,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12368,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12368,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12368,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12368,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12368,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12368,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12368,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12368,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12368,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12368 : FrameRepair 12368 scalarRow12368 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12368Cells j).1 (repair12368Cells j).2.1
  endpoint_upper := fun j => ((repair12368Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12368Cells j).2.2

theorem repair12369Cells (j : Fin 43) :
    0 ≤ (scalarRow12369.table (sourceIndex j)).upper ∧
    (scalarRow12369.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12369.table (sourceIndex j)).centre) /
      (scalarRow12369.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12369.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12369,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12369,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12369,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12369,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12369,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12369,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12369,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12369,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12369,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12369,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12369,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12369,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12369,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12369,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12369,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12369,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12369,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12369,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12369,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12369,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12369,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12369,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12369,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12369,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12369,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12369,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12369,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12369,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12369,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12369,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12369,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12369,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12369,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12369,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12369,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12369,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12369,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12369,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12369,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12369,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12369,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12369,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12369,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12369,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12369,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12369,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12369,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12369,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12369,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12369,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12369,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12369,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12369,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12369,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12369,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12369,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12369,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12369,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12369,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12369,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12369,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12369,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12369,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12369,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12369,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12369,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12369,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12369,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12369,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12369,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12369,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12369,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12369,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12369,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12369,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12369,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12369,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12369,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12369,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12369,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12369,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12369,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12369,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12369,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12369,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12369,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12369 : FrameRepair 12369 scalarRow12369 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12369Cells j).1 (repair12369Cells j).2.1
  endpoint_upper := fun j => ((repair12369Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12369Cells j).2.2

theorem repair12370Cells (j : Fin 43) :
    0 ≤ (scalarRow12370.table (sourceIndex j)).upper ∧
    (scalarRow12370.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12370.table (sourceIndex j)).centre) /
      (scalarRow12370.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12370.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12370,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12370,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12370,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12370,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12370,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12370,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12370,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12370,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12370,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12370,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12370,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12370,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12370,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12370,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12370,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12370,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12370,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12370,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12370,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12370,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12370,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12370,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12370,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12370,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12370,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12370,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12370,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12370,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12370,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12370,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12370,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12370,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12370,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12370,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12370,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12370,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12370,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12370,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12370,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12370,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12370,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12370,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12370,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12370,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12370,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12370,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12370,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12370,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12370,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12370,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12370,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12370,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12370,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12370,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12370,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12370,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12370,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12370,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12370,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12370,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12370,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12370,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12370,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12370,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12370,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12370,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12370,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12370,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12370,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12370,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12370,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12370,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12370,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12370,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12370,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12370,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12370,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12370,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12370,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12370,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12370,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12370,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12370,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12370,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12370,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12370,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12370 : FrameRepair 12370 scalarRow12370 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12370Cells j).1 (repair12370Cells j).2.1
  endpoint_upper := fun j => ((repair12370Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12370Cells j).2.2

theorem repair12371Cells (j : Fin 43) :
    0 ≤ (scalarRow12371.table (sourceIndex j)).upper ∧
    (scalarRow12371.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12371.table (sourceIndex j)).centre) /
      (scalarRow12371.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12371.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12371,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12371,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12371,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12371,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12371,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12371,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12371,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12371,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12371,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12371,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12371,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12371,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12371,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12371,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12371,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12371,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12371,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12371,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12371,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12371,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12371,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12371,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12371,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12371,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12371,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12371,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12371,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12371,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12371,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12371,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12371,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12371,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12371,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12371,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12371,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12371,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12371,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12371,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12371,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12371,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12371,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12371,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12371,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12371,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12371,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12371,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12371,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12371,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12371,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12371,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12371,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12371,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12371,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12371,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12371,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12371,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12371,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12371,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12371,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12371,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12371,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12371,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12371,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12371,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12371,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12371,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12371,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12371,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12371,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12371,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12371,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12371,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12371,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12371,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12371,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12371,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12371,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12371,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12371,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12371,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12371,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12371,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12371,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12371,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12371,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12371,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12371 : FrameRepair 12371 scalarRow12371 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12371Cells j).1 (repair12371Cells j).2.1
  endpoint_upper := fun j => ((repair12371Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12371Cells j).2.2

theorem repair12372Cells (j : Fin 43) :
    0 ≤ (scalarRow12372.table (sourceIndex j)).upper ∧
    (scalarRow12372.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12372.table (sourceIndex j)).centre) /
      (scalarRow12372.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12372.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12372,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12372,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12372,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12372,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12372,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12372,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12372,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12372,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12372,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12372,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12372,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12372,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12372,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12372,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12372,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12372,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12372,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12372,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12372,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12372,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12372,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12372,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12372,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12372,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12372,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12372,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12372,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12372,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12372,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12372,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12372,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12372,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12372,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12372,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12372,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12372,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12372,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12372,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12372,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12372,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12372,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12372,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12372,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12372,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12372,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12372,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12372,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12372,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12372,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12372,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12372,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12372,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12372,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12372,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12372,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12372,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12372,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12372,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12372,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12372,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12372,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12372,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12372,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12372,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12372,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12372,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12372,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12372,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12372,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12372,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12372,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12372,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12372,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12372,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12372,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12372,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12372,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12372,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12372,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12372,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12372,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12372,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12372,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12372,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12372,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12372,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12372 : FrameRepair 12372 scalarRow12372 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12372Cells j).1 (repair12372Cells j).2.1
  endpoint_upper := fun j => ((repair12372Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12372Cells j).2.2

theorem repair12373Cells (j : Fin 43) :
    0 ≤ (scalarRow12373.table (sourceIndex j)).upper ∧
    (scalarRow12373.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12373.table (sourceIndex j)).centre) /
      (scalarRow12373.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12373.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12373,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12373,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12373,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12373,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12373,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12373,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12373,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12373,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12373,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12373,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12373,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12373,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12373,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12373,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12373,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12373,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12373,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12373,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12373,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12373,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12373,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12373,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12373,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12373,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12373,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12373,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12373,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12373,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12373,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12373,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12373,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12373,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12373,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12373,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12373,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12373,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12373,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12373,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12373,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12373,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12373,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12373,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12373,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12373,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12373,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12373,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12373,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12373,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12373,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12373,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12373,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12373,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12373,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12373,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12373,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12373,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12373,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12373,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12373,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12373,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12373,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12373,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12373,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12373,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12373,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12373,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12373,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12373,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12373,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12373,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12373,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12373,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12373,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12373,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12373,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12373,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12373,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12373,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12373,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12373,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12373,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12373,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12373,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12373,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12373,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12373,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12373 : FrameRepair 12373 scalarRow12373 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12373Cells j).1 (repair12373Cells j).2.1
  endpoint_upper := fun j => ((repair12373Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12373Cells j).2.2

theorem repair12374Cells (j : Fin 43) :
    0 ≤ (scalarRow12374.table (sourceIndex j)).upper ∧
    (scalarRow12374.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow12374.table (sourceIndex j)).centre) /
      (scalarRow12374.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12374.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow12374,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12374,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow12374,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12374,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow12374,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12374,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow12374,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12374,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow12374,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12374,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow12374,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12374,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow12374,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12374,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow12374,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12374,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow12374,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12374,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow12374,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12374,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow12374,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12374,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow12374,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12374,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow12374,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12374,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow12374,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12374,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow12374,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12374,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow12374,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12374,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow12374,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12374,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow12374,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12374,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow12374,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12374,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow12374,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12374,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow12374,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12374,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow12374,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12374,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow12374,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12374,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow12374,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12374,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow12374,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12374,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow12374,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12374,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow12374,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12374,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow12374,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12374,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow12374,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12374,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow12374,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12374,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow12374,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12374,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow12374,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12374,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow12374,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12374,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow12374,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12374,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow12374,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12374,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow12374,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12374,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow12374,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12374,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow12374,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12374,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow12374,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12374,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow12374,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12374,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow12374,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12374,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow12374,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12374,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow12374,scalarRow12350,sourceIndex,
      BstLean.Part268.cell12374,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12374 : FrameRepair 12374 scalarRow12374 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair12374Cells j).1 (repair12374Cells j).2.1
  endpoint_upper := fun j => ((repair12374Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair12374Cells j).2.2

end BstLean.Part269
