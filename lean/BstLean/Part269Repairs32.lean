import BstLean.Part269Rows32
import BstLean.Part269RepairCommon
namespace BstLean.Part269
open Real Set BstLean.Part255 BstLean.Part263 BstLean.Part264
theorem repair13150Cells (j : Fin 43) :
    0 ≤ (scalarRow13150.table (sourceIndex j)).upper ∧
    (scalarRow13150.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13150.table (sourceIndex j)).centre) /
      (scalarRow13150.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13150.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13150,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13150,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13150,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13150,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13150,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13150,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13150,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13150,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13150,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13150,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13150,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13150,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13150,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13150,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13150,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13150,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13150,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13150,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13150,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13150,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13150,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13150,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13150,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13150,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13150,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13150,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13150,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13150,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13150,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13150,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13150,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13150,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13150,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13150,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13150,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13150,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13150,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13150,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13150,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13150,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13150,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13150,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13150,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13150,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13150,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13150,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13150,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13150,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13150,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13150,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13150,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13150,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13150,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13150,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13150,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13150,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13150,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13150,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13150,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13150,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13150,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13150,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13150,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13150,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13150,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13150,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13150,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13150,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13150,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13150,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13150,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13150,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13150,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13150,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13150,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13150,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13150,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13150,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13150,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13150,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13150,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13150,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13150,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13150,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13150,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13150,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13150 : FrameRepair 13150 scalarRow13150 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13150Cells j).1 (repair13150Cells j).2.1
  endpoint_upper := fun j => ((repair13150Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13150Cells j).2.2

theorem repair13151Cells (j : Fin 43) :
    0 ≤ (scalarRow13151.table (sourceIndex j)).upper ∧
    (scalarRow13151.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13151.table (sourceIndex j)).centre) /
      (scalarRow13151.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13151.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13151,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13151,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13151,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13151,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13151,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13151,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13151,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13151,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13151,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13151,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13151,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13151,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13151,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13151,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13151,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13151,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13151,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13151,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13151,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13151,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13151,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13151,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13151,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13151,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13151,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13151,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13151,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13151,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13151,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13151,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13151,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13151,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13151,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13151,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13151,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13151,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13151,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13151,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13151,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13151,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13151,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13151,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13151,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13151,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13151,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13151,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13151,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13151,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13151,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13151,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13151,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13151,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13151,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13151,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13151,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13151,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13151,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13151,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13151,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13151,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13151,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13151,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13151,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13151,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13151,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13151,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13151,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13151,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13151,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13151,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13151,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13151,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13151,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13151,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13151,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13151,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13151,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13151,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13151,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13151,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13151,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13151,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13151,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13151,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13151,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13151,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13151 : FrameRepair 13151 scalarRow13151 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13151Cells j).1 (repair13151Cells j).2.1
  endpoint_upper := fun j => ((repair13151Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13151Cells j).2.2

theorem repair13152Cells (j : Fin 43) :
    0 ≤ (scalarRow13152.table (sourceIndex j)).upper ∧
    (scalarRow13152.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13152.table (sourceIndex j)).centre) /
      (scalarRow13152.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13152.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13152,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13152,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13152,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13152,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13152,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13152,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13152,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13152,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13152,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13152,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13152,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13152,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13152,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13152,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13152,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13152,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13152,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13152,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13152,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13152,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13152,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13152,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13152,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13152,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13152,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13152,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13152,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13152,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13152,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13152,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13152,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13152,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13152,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13152,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13152,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13152,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13152,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13152,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13152,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13152,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13152,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13152,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13152,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13152,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13152,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13152,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13152,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13152,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13152,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13152,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13152,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13152,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13152,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13152,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13152,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13152,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13152,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13152,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13152,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13152,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13152,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13152,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13152,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13152,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13152,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13152,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13152,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13152,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13152,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13152,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13152,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13152,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13152,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13152,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13152,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13152,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13152,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13152,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13152,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13152,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13152,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13152,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13152,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13152,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13152,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13152,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13152 : FrameRepair 13152 scalarRow13152 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13152Cells j).1 (repair13152Cells j).2.1
  endpoint_upper := fun j => ((repair13152Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13152Cells j).2.2

theorem repair13153Cells (j : Fin 43) :
    0 ≤ (scalarRow13153.table (sourceIndex j)).upper ∧
    (scalarRow13153.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13153.table (sourceIndex j)).centre) /
      (scalarRow13153.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13153.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13153,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13153,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13153,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13153,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13153,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13153,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13153,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13153,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13153,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13153,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13153,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13153,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13153,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13153,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13153,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13153,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13153,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13153,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13153,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13153,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13153,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13153,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13153,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13153,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13153,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13153,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13153,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13153,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13153,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13153,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13153,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13153,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13153,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13153,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13153,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13153,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13153,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13153,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13153,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13153,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13153,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13153,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13153,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13153,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13153,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13153,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13153,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13153,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13153,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13153,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13153,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13153,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13153,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13153,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13153,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13153,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13153,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13153,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13153,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13153,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13153,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13153,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13153,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13153,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13153,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13153,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13153,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13153,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13153,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13153,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13153,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13153,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13153,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13153,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13153,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13153,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13153,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13153,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13153,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13153,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13153,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13153,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13153,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13153,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13153,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13153,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13153 : FrameRepair 13153 scalarRow13153 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13153Cells j).1 (repair13153Cells j).2.1
  endpoint_upper := fun j => ((repair13153Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13153Cells j).2.2

theorem repair13154Cells (j : Fin 43) :
    0 ≤ (scalarRow13154.table (sourceIndex j)).upper ∧
    (scalarRow13154.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13154.table (sourceIndex j)).centre) /
      (scalarRow13154.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13154.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13154,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13154,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13154,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13154,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13154,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13154,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13154,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13154,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13154,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13154,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13154,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13154,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13154,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13154,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13154,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13154,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13154,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13154,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13154,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13154,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13154,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13154,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13154,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13154,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13154,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13154,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13154,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13154,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13154,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13154,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13154,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13154,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13154,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13154,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13154,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13154,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13154,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13154,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13154,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13154,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13154,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13154,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13154,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13154,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13154,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13154,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13154,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13154,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13154,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13154,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13154,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13154,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13154,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13154,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13154,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13154,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13154,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13154,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13154,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13154,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13154,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13154,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13154,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13154,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13154,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13154,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13154,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13154,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13154,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13154,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13154,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13154,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13154,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13154,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13154,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13154,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13154,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13154,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13154,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13154,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13154,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13154,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13154,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13154,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13154,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13154,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13154 : FrameRepair 13154 scalarRow13154 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13154Cells j).1 (repair13154Cells j).2.1
  endpoint_upper := fun j => ((repair13154Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13154Cells j).2.2

theorem repair13155Cells (j : Fin 43) :
    0 ≤ (scalarRow13155.table (sourceIndex j)).upper ∧
    (scalarRow13155.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13155.table (sourceIndex j)).centre) /
      (scalarRow13155.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13155.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13155,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13155,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13155,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13155,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13155,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13155,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13155,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13155,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13155,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13155,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13155,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13155,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13155,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13155,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13155,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13155,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13155,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13155,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13155,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13155,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13155,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13155,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13155,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13155,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13155,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13155,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13155,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13155,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13155,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13155,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13155,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13155,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13155,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13155,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13155,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13155,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13155,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13155,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13155,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13155,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13155,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13155,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13155,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13155,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13155,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13155,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13155,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13155,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13155,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13155,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13155,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13155,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13155,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13155,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13155,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13155,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13155,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13155,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13155,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13155,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13155,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13155,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13155,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13155,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13155,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13155,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13155,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13155,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13155,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13155,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13155,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13155,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13155,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13155,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13155,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13155,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13155,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13155,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13155,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13155,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13155,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13155,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13155,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13155,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13155,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13155,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13155 : FrameRepair 13155 scalarRow13155 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13155Cells j).1 (repair13155Cells j).2.1
  endpoint_upper := fun j => ((repair13155Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13155Cells j).2.2

theorem repair13156Cells (j : Fin 43) :
    0 ≤ (scalarRow13156.table (sourceIndex j)).upper ∧
    (scalarRow13156.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13156.table (sourceIndex j)).centre) /
      (scalarRow13156.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13156.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13156,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13156,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13156,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13156,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13156,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13156,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13156,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13156,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13156,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13156,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13156,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13156,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13156,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13156,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13156,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13156,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13156,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13156,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13156,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13156,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13156,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13156,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13156,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13156,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13156,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13156,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13156,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13156,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13156,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13156,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13156,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13156,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13156,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13156,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13156,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13156,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13156,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13156,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13156,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13156,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13156,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13156,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13156,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13156,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13156,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13156,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13156,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13156,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13156,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13156,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13156,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13156,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13156,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13156,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13156,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13156,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13156,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13156,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13156,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13156,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13156,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13156,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13156,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13156,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13156,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13156,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13156,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13156,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13156,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13156,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13156,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13156,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13156,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13156,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13156,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13156,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13156,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13156,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13156,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13156,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13156,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13156,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13156,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13156,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13156,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13156,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13156 : FrameRepair 13156 scalarRow13156 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13156Cells j).1 (repair13156Cells j).2.1
  endpoint_upper := fun j => ((repair13156Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13156Cells j).2.2

theorem repair13157Cells (j : Fin 43) :
    0 ≤ (scalarRow13157.table (sourceIndex j)).upper ∧
    (scalarRow13157.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13157.table (sourceIndex j)).centre) /
      (scalarRow13157.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13157.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13157,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13157,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13157,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13157,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13157,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13157,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13157,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13157,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13157,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13157,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13157,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13157,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13157,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13157,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13157,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13157,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13157,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13157,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13157,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13157,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13157,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13157,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13157,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13157,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13157,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13157,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13157,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13157,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13157,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13157,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13157,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13157,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13157,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13157,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13157,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13157,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13157,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13157,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13157,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13157,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13157,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13157,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13157,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13157,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13157,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13157,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13157,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13157,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13157,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13157,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13157,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13157,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13157,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13157,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13157,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13157,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13157,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13157,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13157,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13157,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13157,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13157,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13157,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13157,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13157,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13157,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13157,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13157,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13157,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13157,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13157,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13157,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13157,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13157,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13157,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13157,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13157,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13157,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13157,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13157,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13157,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13157,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13157,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13157,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13157,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13157,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13157 : FrameRepair 13157 scalarRow13157 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13157Cells j).1 (repair13157Cells j).2.1
  endpoint_upper := fun j => ((repair13157Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13157Cells j).2.2

theorem repair13158Cells (j : Fin 43) :
    0 ≤ (scalarRow13158.table (sourceIndex j)).upper ∧
    (scalarRow13158.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13158.table (sourceIndex j)).centre) /
      (scalarRow13158.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13158.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13158,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13158,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13158,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13158,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13158,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13158,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13158,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13158,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13158,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13158,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13158,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13158,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13158,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13158,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13158,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13158,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13158,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13158,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13158,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13158,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13158,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13158,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13158,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13158,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13158,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13158,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13158,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13158,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13158,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13158,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13158,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13158,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13158,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13158,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13158,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13158,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13158,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13158,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13158,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13158,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13158,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13158,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13158,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13158,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13158,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13158,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13158,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13158,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13158,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13158,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13158,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13158,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13158,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13158,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13158,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13158,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13158,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13158,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13158,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13158,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13158,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13158,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13158,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13158,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13158,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13158,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13158,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13158,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13158,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13158,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13158,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13158,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13158,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13158,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13158,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13158,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13158,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13158,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13158,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13158,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13158,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13158,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13158,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13158,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13158,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13158,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13158 : FrameRepair 13158 scalarRow13158 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13158Cells j).1 (repair13158Cells j).2.1
  endpoint_upper := fun j => ((repair13158Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13158Cells j).2.2

theorem repair13159Cells (j : Fin 43) :
    0 ≤ (scalarRow13159.table (sourceIndex j)).upper ∧
    (scalarRow13159.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13159.table (sourceIndex j)).centre) /
      (scalarRow13159.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13159.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13159,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13159,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13159,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13159,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13159,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13159,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13159,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13159,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13159,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13159,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13159,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13159,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13159,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13159,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13159,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13159,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13159,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13159,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13159,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13159,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13159,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13159,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13159,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13159,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13159,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13159,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13159,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13159,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13159,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13159,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13159,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13159,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13159,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13159,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13159,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13159,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13159,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13159,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13159,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13159,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13159,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13159,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13159,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13159,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13159,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13159,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13159,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13159,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13159,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13159,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13159,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13159,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13159,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13159,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13159,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13159,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13159,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13159,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13159,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13159,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13159,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13159,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13159,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13159,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13159,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13159,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13159,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13159,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13159,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13159,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13159,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13159,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13159,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13159,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13159,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13159,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13159,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13159,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13159,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13159,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13159,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13159,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13159,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13159,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13159,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13159,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13159 : FrameRepair 13159 scalarRow13159 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13159Cells j).1 (repair13159Cells j).2.1
  endpoint_upper := fun j => ((repair13159Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13159Cells j).2.2

theorem repair13160Cells (j : Fin 43) :
    0 ≤ (scalarRow13160.table (sourceIndex j)).upper ∧
    (scalarRow13160.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13160.table (sourceIndex j)).centre) /
      (scalarRow13160.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13160.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13160,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13160,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13160,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13160,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13160,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13160,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13160,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13160,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13160,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13160,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13160,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13160,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13160,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13160,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13160,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13160,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13160,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13160,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13160,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13160,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13160,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13160,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13160,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13160,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13160,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13160,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13160,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13160,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13160,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13160,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13160,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13160,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13160,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13160,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13160,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13160,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13160,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13160,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13160,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13160,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13160,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13160,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13160,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13160,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13160,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13160,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13160,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13160,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13160,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13160,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13160,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13160,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13160,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13160,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13160,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13160,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13160,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13160,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13160,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13160,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13160,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13160,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13160,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13160,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13160,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13160,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13160,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13160,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13160,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13160,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13160,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13160,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13160,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13160,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13160,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13160,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13160,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13160,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13160,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13160,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13160,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13160,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13160,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13160,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13160,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13160,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13160 : FrameRepair 13160 scalarRow13160 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13160Cells j).1 (repair13160Cells j).2.1
  endpoint_upper := fun j => ((repair13160Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13160Cells j).2.2

theorem repair13161Cells (j : Fin 43) :
    0 ≤ (scalarRow13161.table (sourceIndex j)).upper ∧
    (scalarRow13161.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13161.table (sourceIndex j)).centre) /
      (scalarRow13161.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13161.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13161,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13161,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13161,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13161,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13161,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13161,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13161,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13161,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13161,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13161,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13161,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13161,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13161,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13161,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13161,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13161,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13161,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13161,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13161,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13161,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13161,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13161,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13161,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13161,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13161,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13161,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13161,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13161,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13161,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13161,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13161,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13161,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13161,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13161,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13161,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13161,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13161,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13161,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13161,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13161,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13161,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13161,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13161,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13161,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13161,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13161,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13161,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13161,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13161,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13161,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13161,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13161,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13161,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13161,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13161,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13161,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13161,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13161,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13161,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13161,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13161,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13161,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13161,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13161,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13161,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13161,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13161,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13161,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13161,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13161,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13161,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13161,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13161,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13161,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13161,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13161,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13161,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13161,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13161,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13161,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13161,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13161,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13161,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13161,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13161,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13161,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13161 : FrameRepair 13161 scalarRow13161 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13161Cells j).1 (repair13161Cells j).2.1
  endpoint_upper := fun j => ((repair13161Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13161Cells j).2.2

theorem repair13162Cells (j : Fin 43) :
    0 ≤ (scalarRow13162.table (sourceIndex j)).upper ∧
    (scalarRow13162.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13162.table (sourceIndex j)).centre) /
      (scalarRow13162.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13162.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13162,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13162,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13162,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13162,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13162,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13162,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13162,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13162,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13162,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13162,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13162,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13162,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13162,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13162,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13162,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13162,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13162,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13162,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13162,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13162,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13162,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13162,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13162,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13162,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13162,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13162,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13162,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13162,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13162,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13162,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13162,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13162,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13162,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13162,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13162,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13162,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13162,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13162,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13162,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13162,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13162,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13162,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13162,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13162,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13162,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13162,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13162,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13162,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13162,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13162,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13162,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13162,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13162,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13162,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13162,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13162,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13162,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13162,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13162,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13162,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13162,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13162,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13162,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13162,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13162,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13162,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13162,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13162,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13162,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13162,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13162,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13162,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13162,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13162,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13162,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13162,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13162,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13162,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13162,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13162,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13162,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13162,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13162,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13162,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13162,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13162,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13162 : FrameRepair 13162 scalarRow13162 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13162Cells j).1 (repair13162Cells j).2.1
  endpoint_upper := fun j => ((repair13162Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13162Cells j).2.2

theorem repair13163Cells (j : Fin 43) :
    0 ≤ (scalarRow13163.table (sourceIndex j)).upper ∧
    (scalarRow13163.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13163.table (sourceIndex j)).centre) /
      (scalarRow13163.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13163.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13163,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13163,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13163,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13163,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13163,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13163,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13163,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13163,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13163,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13163,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13163,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13163,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13163,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13163,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13163,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13163,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13163,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13163,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13163,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13163,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13163,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13163,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13163,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13163,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13163,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13163,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13163,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13163,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13163,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13163,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13163,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13163,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13163,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13163,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13163,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13163,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13163,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13163,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13163,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13163,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13163,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13163,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13163,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13163,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13163,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13163,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13163,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13163,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13163,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13163,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13163,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13163,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13163,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13163,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13163,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13163,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13163,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13163,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13163,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13163,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13163,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13163,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13163,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13163,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13163,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13163,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13163,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13163,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13163,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13163,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13163,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13163,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13163,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13163,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13163,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13163,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13163,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13163,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13163,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13163,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13163,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13163,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13163,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13163,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13163,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13163,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13163 : FrameRepair 13163 scalarRow13163 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13163Cells j).1 (repair13163Cells j).2.1
  endpoint_upper := fun j => ((repair13163Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13163Cells j).2.2

theorem repair13164Cells (j : Fin 43) :
    0 ≤ (scalarRow13164.table (sourceIndex j)).upper ∧
    (scalarRow13164.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13164.table (sourceIndex j)).centre) /
      (scalarRow13164.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13164.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13164,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13164,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13164,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13164,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13164,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13164,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13164,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13164,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13164,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13164,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13164,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13164,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13164,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13164,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13164,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13164,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13164,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13164,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13164,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13164,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13164,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13164,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13164,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13164,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13164,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13164,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13164,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13164,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13164,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13164,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13164,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13164,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13164,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13164,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13164,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13164,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13164,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13164,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13164,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13164,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13164,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13164,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13164,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13164,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13164,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13164,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13164,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13164,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13164,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13164,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13164,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13164,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13164,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13164,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13164,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13164,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13164,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13164,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13164,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13164,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13164,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13164,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13164,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13164,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13164,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13164,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13164,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13164,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13164,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13164,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13164,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13164,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13164,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13164,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13164,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13164,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13164,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13164,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13164,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13164,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13164,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13164,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13164,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13164,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13164,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13164,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13164 : FrameRepair 13164 scalarRow13164 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13164Cells j).1 (repair13164Cells j).2.1
  endpoint_upper := fun j => ((repair13164Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13164Cells j).2.2

theorem repair13165Cells (j : Fin 43) :
    0 ≤ (scalarRow13165.table (sourceIndex j)).upper ∧
    (scalarRow13165.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13165.table (sourceIndex j)).centre) /
      (scalarRow13165.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13165.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13165,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13165,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13165,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13165,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13165,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13165,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13165,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13165,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13165,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13165,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13165,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13165,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13165,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13165,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13165,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13165,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13165,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13165,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13165,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13165,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13165,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13165,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13165,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13165,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13165,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13165,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13165,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13165,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13165,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13165,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13165,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13165,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13165,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13165,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13165,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13165,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13165,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13165,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13165,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13165,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13165,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13165,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13165,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13165,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13165,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13165,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13165,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13165,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13165,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13165,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13165,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13165,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13165,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13165,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13165,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13165,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13165,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13165,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13165,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13165,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13165,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13165,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13165,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13165,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13165,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13165,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13165,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13165,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13165,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13165,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13165,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13165,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13165,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13165,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13165,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13165,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13165,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13165,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13165,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13165,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13165,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13165,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13165,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13165,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13165,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13165,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13165 : FrameRepair 13165 scalarRow13165 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13165Cells j).1 (repair13165Cells j).2.1
  endpoint_upper := fun j => ((repair13165Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13165Cells j).2.2

theorem repair13166Cells (j : Fin 43) :
    0 ≤ (scalarRow13166.table (sourceIndex j)).upper ∧
    (scalarRow13166.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13166.table (sourceIndex j)).centre) /
      (scalarRow13166.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13166.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13166,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13166,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13166,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13166,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13166,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13166,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13166,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13166,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13166,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13166,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13166,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13166,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13166,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13166,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13166,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13166,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13166,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13166,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13166,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13166,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13166,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13166,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13166,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13166,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13166,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13166,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13166,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13166,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13166,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13166,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13166,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13166,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13166,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13166,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13166,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13166,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13166,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13166,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13166,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13166,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13166,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13166,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13166,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13166,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13166,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13166,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13166,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13166,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13166,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13166,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13166,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13166,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13166,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13166,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13166,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13166,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13166,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13166,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13166,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13166,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13166,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13166,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13166,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13166,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13166,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13166,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13166,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13166,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13166,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13166,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13166,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13166,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13166,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13166,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13166,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13166,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13166,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13166,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13166,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13166,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13166,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13166,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13166,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13166,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13166,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13166,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13166 : FrameRepair 13166 scalarRow13166 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13166Cells j).1 (repair13166Cells j).2.1
  endpoint_upper := fun j => ((repair13166Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13166Cells j).2.2

theorem repair13167Cells (j : Fin 43) :
    0 ≤ (scalarRow13167.table (sourceIndex j)).upper ∧
    (scalarRow13167.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13167.table (sourceIndex j)).centre) /
      (scalarRow13167.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13167.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13167,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13167,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13167,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13167,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13167,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13167,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13167,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13167,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13167,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13167,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13167,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13167,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13167,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13167,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13167,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13167,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13167,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13167,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13167,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13167,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13167,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13167,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13167,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13167,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13167,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13167,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13167,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13167,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13167,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13167,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13167,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13167,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13167,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13167,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13167,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13167,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13167,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13167,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13167,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13167,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13167,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13167,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13167,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13167,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13167,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13167,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13167,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13167,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13167,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13167,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13167,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13167,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13167,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13167,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13167,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13167,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13167,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13167,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13167,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13167,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13167,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13167,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13167,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13167,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13167,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13167,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13167,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13167,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13167,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13167,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13167,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13167,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13167,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13167,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13167,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13167,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13167,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13167,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13167,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13167,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13167,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13167,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13167,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13167,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13167,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13167,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13167 : FrameRepair 13167 scalarRow13167 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13167Cells j).1 (repair13167Cells j).2.1
  endpoint_upper := fun j => ((repair13167Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13167Cells j).2.2

theorem repair13168Cells (j : Fin 43) :
    0 ≤ (scalarRow13168.table (sourceIndex j)).upper ∧
    (scalarRow13168.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13168.table (sourceIndex j)).centre) /
      (scalarRow13168.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13168.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13168,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13168,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13168,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13168,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13168,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13168,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13168,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13168,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13168,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13168,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13168,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13168,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13168,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13168,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13168,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13168,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13168,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13168,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13168,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13168,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13168,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13168,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13168,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13168,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13168,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13168,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13168,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13168,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13168,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13168,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13168,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13168,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13168,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13168,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13168,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13168,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13168,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13168,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13168,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13168,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13168,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13168,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13168,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13168,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13168,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13168,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13168,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13168,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13168,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13168,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13168,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13168,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13168,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13168,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13168,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13168,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13168,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13168,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13168,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13168,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13168,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13168,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13168,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13168,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13168,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13168,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13168,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13168,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13168,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13168,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13168,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13168,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13168,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13168,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13168,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13168,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13168,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13168,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13168,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13168,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13168,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13168,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13168,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13168,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13168,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13168,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13168 : FrameRepair 13168 scalarRow13168 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13168Cells j).1 (repair13168Cells j).2.1
  endpoint_upper := fun j => ((repair13168Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13168Cells j).2.2

theorem repair13169Cells (j : Fin 43) :
    0 ≤ (scalarRow13169.table (sourceIndex j)).upper ∧
    (scalarRow13169.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13169.table (sourceIndex j)).centre) /
      (scalarRow13169.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13169.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13169,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13169,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13169,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13169,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13169,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13169,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13169,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13169,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13169,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13169,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13169,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13169,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13169,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13169,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13169,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13169,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13169,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13169,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13169,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13169,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13169,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13169,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13169,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13169,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13169,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13169,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13169,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13169,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13169,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13169,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13169,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13169,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13169,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13169,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13169,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13169,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13169,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13169,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13169,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13169,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13169,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13169,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13169,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13169,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13169,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13169,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13169,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13169,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13169,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13169,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13169,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13169,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13169,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13169,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13169,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13169,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13169,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13169,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13169,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13169,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13169,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13169,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13169,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13169,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13169,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13169,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13169,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13169,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13169,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13169,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13169,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13169,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13169,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13169,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13169,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13169,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13169,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13169,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13169,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13169,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13169,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13169,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13169,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13169,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13169,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13169,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13169 : FrameRepair 13169 scalarRow13169 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13169Cells j).1 (repair13169Cells j).2.1
  endpoint_upper := fun j => ((repair13169Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13169Cells j).2.2

theorem repair13170Cells (j : Fin 43) :
    0 ≤ (scalarRow13170.table (sourceIndex j)).upper ∧
    (scalarRow13170.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13170.table (sourceIndex j)).centre) /
      (scalarRow13170.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13170.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13170,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13170,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13170,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13170,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13170,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13170,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13170,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13170,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13170,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13170,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13170,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13170,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13170,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13170,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13170,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13170,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13170,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13170,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13170,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13170,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13170,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13170,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13170,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13170,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13170,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13170,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13170,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13170,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13170,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13170,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13170,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13170,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13170,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13170,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13170,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13170,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13170,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13170,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13170,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13170,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13170,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13170,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13170,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13170,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13170,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13170,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13170,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13170,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13170,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13170,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13170,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13170,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13170,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13170,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13170,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13170,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13170,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13170,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13170,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13170,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13170,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13170,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13170,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13170,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13170,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13170,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13170,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13170,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13170,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13170,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13170,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13170,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13170,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13170,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13170,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13170,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13170,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13170,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13170,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13170,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13170,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13170,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13170,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13170,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13170,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13170,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13170 : FrameRepair 13170 scalarRow13170 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13170Cells j).1 (repair13170Cells j).2.1
  endpoint_upper := fun j => ((repair13170Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13170Cells j).2.2

theorem repair13171Cells (j : Fin 43) :
    0 ≤ (scalarRow13171.table (sourceIndex j)).upper ∧
    (scalarRow13171.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13171.table (sourceIndex j)).centre) /
      (scalarRow13171.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13171.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13171,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13171,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13171,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13171,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13171,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13171,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13171,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13171,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13171,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13171,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13171,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13171,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13171,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13171,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13171,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13171,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13171,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13171,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13171,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13171,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13171,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13171,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13171,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13171,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13171,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13171,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13171,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13171,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13171,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13171,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13171,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13171,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13171,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13171,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13171,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13171,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13171,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13171,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13171,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13171,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13171,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13171,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13171,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13171,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13171,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13171,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13171,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13171,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13171,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13171,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13171,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13171,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13171,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13171,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13171,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13171,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13171,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13171,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13171,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13171,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13171,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13171,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13171,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13171,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13171,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13171,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13171,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13171,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13171,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13171,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13171,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13171,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13171,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13171,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13171,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13171,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13171,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13171,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13171,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13171,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13171,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13171,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13171,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13171,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13171,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13171,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13171 : FrameRepair 13171 scalarRow13171 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13171Cells j).1 (repair13171Cells j).2.1
  endpoint_upper := fun j => ((repair13171Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13171Cells j).2.2

theorem repair13172Cells (j : Fin 43) :
    0 ≤ (scalarRow13172.table (sourceIndex j)).upper ∧
    (scalarRow13172.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13172.table (sourceIndex j)).centre) /
      (scalarRow13172.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13172.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13172,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13172,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13172,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13172,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13172,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13172,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13172,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13172,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13172,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13172,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13172,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13172,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13172,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13172,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13172,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13172,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13172,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13172,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13172,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13172,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13172,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13172,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13172,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13172,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13172,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13172,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13172,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13172,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13172,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13172,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13172,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13172,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13172,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13172,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13172,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13172,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13172,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13172,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13172,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13172,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13172,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13172,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13172,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13172,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13172,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13172,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13172,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13172,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13172,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13172,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13172,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13172,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13172,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13172,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13172,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13172,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13172,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13172,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13172,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13172,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13172,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13172,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13172,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13172,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13172,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13172,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13172,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13172,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13172,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13172,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13172,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13172,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13172,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13172,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13172,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13172,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13172,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13172,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13172,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13172,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13172,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13172,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13172,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13172,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13172,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13172,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13172 : FrameRepair 13172 scalarRow13172 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13172Cells j).1 (repair13172Cells j).2.1
  endpoint_upper := fun j => ((repair13172Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13172Cells j).2.2

theorem repair13173Cells (j : Fin 43) :
    0 ≤ (scalarRow13173.table (sourceIndex j)).upper ∧
    (scalarRow13173.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13173.table (sourceIndex j)).centre) /
      (scalarRow13173.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13173.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13173,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13173,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13173,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13173,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13173,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13173,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13173,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13173,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13173,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13173,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13173,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13173,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13173,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13173,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13173,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13173,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13173,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13173,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13173,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13173,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13173,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13173,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13173,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13173,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13173,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13173,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13173,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13173,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13173,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13173,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13173,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13173,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13173,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13173,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13173,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13173,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13173,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13173,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13173,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13173,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13173,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13173,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13173,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13173,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13173,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13173,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13173,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13173,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13173,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13173,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13173,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13173,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13173,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13173,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13173,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13173,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13173,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13173,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13173,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13173,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13173,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13173,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13173,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13173,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13173,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13173,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13173,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13173,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13173,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13173,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13173,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13173,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13173,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13173,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13173,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13173,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13173,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13173,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13173,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13173,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13173,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13173,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13173,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13173,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13173,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13173,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13173 : FrameRepair 13173 scalarRow13173 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13173Cells j).1 (repair13173Cells j).2.1
  endpoint_upper := fun j => ((repair13173Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13173Cells j).2.2

theorem repair13174Cells (j : Fin 43) :
    0 ≤ (scalarRow13174.table (sourceIndex j)).upper ∧
    (scalarRow13174.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13174.table (sourceIndex j)).centre) /
      (scalarRow13174.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13174.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13174,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13174,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13174,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13174,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13174,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13174,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13174,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13174,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13174,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13174,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13174,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13174,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13174,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13174,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13174,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13174,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13174,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13174,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13174,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13174,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13174,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13174,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13174,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13174,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13174,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13174,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13174,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13174,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13174,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13174,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13174,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13174,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13174,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13174,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13174,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13174,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13174,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13174,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13174,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13174,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13174,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13174,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13174,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13174,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13174,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13174,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13174,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13174,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13174,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13174,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13174,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13174,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13174,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13174,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13174,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13174,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13174,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13174,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13174,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13174,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13174,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13174,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13174,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13174,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13174,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13174,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13174,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13174,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13174,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13174,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13174,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13174,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13174,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13174,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13174,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13174,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13174,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13174,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13174,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13174,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13174,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13174,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13174,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13174,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13174,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13174,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13174 : FrameRepair 13174 scalarRow13174 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13174Cells j).1 (repair13174Cells j).2.1
  endpoint_upper := fun j => ((repair13174Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13174Cells j).2.2

end BstLean.Part269
