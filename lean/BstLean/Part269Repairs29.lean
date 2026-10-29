import BstLean.Part269Rows29
import BstLean.Part269RepairCommon
namespace BstLean.Part269
open Real Set BstLean.Part255 BstLean.Part263 BstLean.Part264
theorem repair13075Cells (j : Fin 43) :
    0 ≤ (scalarRow13075.table (sourceIndex j)).upper ∧
    (scalarRow13075.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13075.table (sourceIndex j)).centre) /
      (scalarRow13075.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13075.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13075,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13075,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13075,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13075,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13075,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13075,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13075,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13075,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13075,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13075,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13075,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13075,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13075,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13075,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13075,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13075,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13075,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13075,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13075,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13075,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13075,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13075,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13075,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13075,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13075,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13075,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13075,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13075,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13075,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13075,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13075,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13075,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13075,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13075,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13075,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13075,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13075,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13075,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13075,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13075,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13075,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13075,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13075,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13075,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13075,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13075,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13075,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13075,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13075,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13075,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13075,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13075,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13075,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13075,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13075,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13075,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13075,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13075,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13075,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13075,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13075,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13075,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13075,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13075,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13075,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13075,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13075,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13075,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13075,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13075,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13075,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13075,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13075,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13075,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13075,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13075,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13075,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13075,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13075,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13075,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13075,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13075,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13075,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13075,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13075,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13075,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13075 : FrameRepair 13075 scalarRow13075 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13075Cells j).1 (repair13075Cells j).2.1
  endpoint_upper := fun j => ((repair13075Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13075Cells j).2.2

theorem repair13076Cells (j : Fin 43) :
    0 ≤ (scalarRow13076.table (sourceIndex j)).upper ∧
    (scalarRow13076.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13076.table (sourceIndex j)).centre) /
      (scalarRow13076.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13076.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13076,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13076,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13076,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13076,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13076,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13076,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13076,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13076,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13076,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13076,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13076,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13076,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13076,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13076,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13076,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13076,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13076,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13076,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13076,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13076,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13076,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13076,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13076,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13076,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13076,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13076,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13076,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13076,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13076,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13076,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13076,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13076,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13076,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13076,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13076,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13076,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13076,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13076,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13076,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13076,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13076,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13076,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13076,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13076,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13076,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13076,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13076,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13076,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13076,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13076,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13076,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13076,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13076,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13076,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13076,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13076,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13076,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13076,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13076,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13076,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13076,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13076,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13076,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13076,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13076,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13076,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13076,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13076,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13076,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13076,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13076,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13076,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13076,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13076,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13076,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13076,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13076,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13076,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13076,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13076,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13076,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13076,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13076,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13076,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13076,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13076,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13076 : FrameRepair 13076 scalarRow13076 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13076Cells j).1 (repair13076Cells j).2.1
  endpoint_upper := fun j => ((repair13076Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13076Cells j).2.2

theorem repair13077Cells (j : Fin 43) :
    0 ≤ (scalarRow13077.table (sourceIndex j)).upper ∧
    (scalarRow13077.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13077.table (sourceIndex j)).centre) /
      (scalarRow13077.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13077.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13077,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13077,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13077,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13077,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13077,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13077,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13077,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13077,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13077,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13077,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13077,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13077,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13077,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13077,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13077,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13077,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13077,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13077,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13077,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13077,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13077,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13077,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13077,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13077,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13077,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13077,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13077,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13077,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13077,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13077,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13077,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13077,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13077,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13077,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13077,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13077,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13077,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13077,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13077,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13077,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13077,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13077,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13077,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13077,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13077,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13077,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13077,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13077,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13077,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13077,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13077,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13077,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13077,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13077,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13077,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13077,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13077,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13077,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13077,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13077,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13077,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13077,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13077,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13077,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13077,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13077,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13077,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13077,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13077,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13077,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13077,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13077,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13077,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13077,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13077,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13077,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13077,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13077,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13077,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13077,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13077,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13077,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13077,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13077,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13077,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13077,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13077 : FrameRepair 13077 scalarRow13077 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13077Cells j).1 (repair13077Cells j).2.1
  endpoint_upper := fun j => ((repair13077Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13077Cells j).2.2

theorem repair13078Cells (j : Fin 43) :
    0 ≤ (scalarRow13078.table (sourceIndex j)).upper ∧
    (scalarRow13078.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13078.table (sourceIndex j)).centre) /
      (scalarRow13078.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13078.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13078,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13078,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13078,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13078,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13078,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13078,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13078,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13078,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13078,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13078,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13078,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13078,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13078,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13078,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13078,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13078,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13078,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13078,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13078,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13078,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13078,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13078,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13078,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13078,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13078,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13078,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13078,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13078,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13078,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13078,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13078,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13078,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13078,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13078,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13078,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13078,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13078,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13078,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13078,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13078,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13078,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13078,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13078,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13078,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13078,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13078,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13078,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13078,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13078,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13078,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13078,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13078,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13078,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13078,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13078,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13078,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13078,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13078,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13078,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13078,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13078,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13078,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13078,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13078,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13078,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13078,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13078,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13078,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13078,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13078,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13078,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13078,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13078,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13078,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13078,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13078,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13078,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13078,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13078,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13078,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13078,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13078,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13078,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13078,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13078,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13078,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13078 : FrameRepair 13078 scalarRow13078 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13078Cells j).1 (repair13078Cells j).2.1
  endpoint_upper := fun j => ((repair13078Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13078Cells j).2.2

theorem repair13079Cells (j : Fin 43) :
    0 ≤ (scalarRow13079.table (sourceIndex j)).upper ∧
    (scalarRow13079.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13079.table (sourceIndex j)).centre) /
      (scalarRow13079.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13079.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13079,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13079,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13079,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13079,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13079,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13079,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13079,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13079,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13079,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13079,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13079,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13079,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13079,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13079,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13079,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13079,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13079,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13079,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13079,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13079,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13079,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13079,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13079,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13079,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13079,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13079,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13079,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13079,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13079,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13079,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13079,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13079,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13079,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13079,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13079,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13079,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13079,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13079,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13079,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13079,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13079,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13079,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13079,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13079,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13079,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13079,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13079,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13079,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13079,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13079,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13079,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13079,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13079,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13079,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13079,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13079,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13079,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13079,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13079,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13079,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13079,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13079,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13079,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13079,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13079,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13079,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13079,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13079,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13079,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13079,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13079,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13079,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13079,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13079,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13079,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13079,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13079,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13079,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13079,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13079,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13079,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13079,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13079,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13079,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13079,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13079,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13079 : FrameRepair 13079 scalarRow13079 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13079Cells j).1 (repair13079Cells j).2.1
  endpoint_upper := fun j => ((repair13079Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13079Cells j).2.2

theorem repair13080Cells (j : Fin 43) :
    0 ≤ (scalarRow13080.table (sourceIndex j)).upper ∧
    (scalarRow13080.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13080.table (sourceIndex j)).centre) /
      (scalarRow13080.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13080.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13080,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13080,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13080,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13080,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13080,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13080,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13080,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13080,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13080,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13080,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13080,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13080,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13080,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13080,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13080,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13080,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13080,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13080,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13080,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13080,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13080,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13080,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13080,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13080,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13080,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13080,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13080,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13080,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13080,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13080,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13080,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13080,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13080,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13080,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13080,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13080,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13080,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13080,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13080,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13080,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13080,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13080,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13080,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13080,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13080,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13080,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13080,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13080,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13080,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13080,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13080,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13080,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13080,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13080,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13080,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13080,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13080,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13080,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13080,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13080,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13080,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13080,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13080,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13080,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13080,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13080,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13080,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13080,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13080,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13080,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13080,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13080,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13080,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13080,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13080,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13080,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13080,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13080,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13080,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13080,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13080,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13080,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13080,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13080,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13080,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13080,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13080 : FrameRepair 13080 scalarRow13080 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13080Cells j).1 (repair13080Cells j).2.1
  endpoint_upper := fun j => ((repair13080Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13080Cells j).2.2

theorem repair13081Cells (j : Fin 43) :
    0 ≤ (scalarRow13081.table (sourceIndex j)).upper ∧
    (scalarRow13081.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13081.table (sourceIndex j)).centre) /
      (scalarRow13081.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13081.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13081,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13081,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13081,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13081,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13081,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13081,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13081,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13081,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13081,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13081,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13081,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13081,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13081,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13081,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13081,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13081,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13081,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13081,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13081,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13081,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13081,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13081,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13081,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13081,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13081,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13081,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13081,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13081,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13081,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13081,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13081,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13081,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13081,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13081,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13081,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13081,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13081,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13081,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13081,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13081,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13081,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13081,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13081,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13081,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13081,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13081,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13081,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13081,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13081,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13081,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13081,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13081,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13081,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13081,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13081,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13081,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13081,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13081,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13081,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13081,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13081,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13081,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13081,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13081,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13081,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13081,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13081,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13081,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13081,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13081,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13081,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13081,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13081,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13081,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13081,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13081,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13081,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13081,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13081,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13081,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13081,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13081,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13081,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13081,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13081,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13081,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13081 : FrameRepair 13081 scalarRow13081 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13081Cells j).1 (repair13081Cells j).2.1
  endpoint_upper := fun j => ((repair13081Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13081Cells j).2.2

theorem repair13082Cells (j : Fin 43) :
    0 ≤ (scalarRow13082.table (sourceIndex j)).upper ∧
    (scalarRow13082.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13082.table (sourceIndex j)).centre) /
      (scalarRow13082.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13082.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13082,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13082,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13082,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13082,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13082,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13082,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13082,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13082,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13082,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13082,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13082,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13082,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13082,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13082,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13082,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13082,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13082,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13082,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13082,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13082,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13082,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13082,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13082,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13082,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13082,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13082,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13082,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13082,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13082,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13082,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13082,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13082,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13082,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13082,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13082,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13082,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13082,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13082,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13082,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13082,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13082,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13082,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13082,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13082,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13082,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13082,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13082,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13082,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13082,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13082,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13082,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13082,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13082,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13082,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13082,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13082,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13082,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13082,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13082,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13082,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13082,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13082,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13082,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13082,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13082,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13082,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13082,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13082,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13082,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13082,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13082,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13082,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13082,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13082,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13082,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13082,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13082,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13082,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13082,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13082,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13082,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13082,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13082,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13082,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13082,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13082,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13082 : FrameRepair 13082 scalarRow13082 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13082Cells j).1 (repair13082Cells j).2.1
  endpoint_upper := fun j => ((repair13082Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13082Cells j).2.2

theorem repair13083Cells (j : Fin 43) :
    0 ≤ (scalarRow13083.table (sourceIndex j)).upper ∧
    (scalarRow13083.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13083.table (sourceIndex j)).centre) /
      (scalarRow13083.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13083.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13083,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13083,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13083,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13083,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13083,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13083,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13083,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13083,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13083,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13083,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13083,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13083,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13083,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13083,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13083,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13083,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13083,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13083,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13083,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13083,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13083,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13083,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13083,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13083,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13083,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13083,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13083,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13083,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13083,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13083,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13083,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13083,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13083,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13083,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13083,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13083,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13083,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13083,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13083,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13083,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13083,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13083,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13083,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13083,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13083,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13083,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13083,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13083,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13083,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13083,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13083,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13083,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13083,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13083,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13083,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13083,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13083,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13083,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13083,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13083,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13083,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13083,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13083,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13083,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13083,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13083,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13083,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13083,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13083,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13083,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13083,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13083,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13083,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13083,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13083,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13083,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13083,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13083,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13083,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13083,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13083,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13083,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13083,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13083,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13083,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13083,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13083 : FrameRepair 13083 scalarRow13083 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13083Cells j).1 (repair13083Cells j).2.1
  endpoint_upper := fun j => ((repair13083Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13083Cells j).2.2

theorem repair13084Cells (j : Fin 43) :
    0 ≤ (scalarRow13084.table (sourceIndex j)).upper ∧
    (scalarRow13084.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13084.table (sourceIndex j)).centre) /
      (scalarRow13084.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13084.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13084,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13084,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13084,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13084,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13084,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13084,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13084,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13084,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13084,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13084,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13084,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13084,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13084,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13084,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13084,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13084,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13084,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13084,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13084,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13084,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13084,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13084,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13084,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13084,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13084,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13084,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13084,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13084,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13084,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13084,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13084,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13084,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13084,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13084,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13084,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13084,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13084,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13084,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13084,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13084,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13084,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13084,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13084,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13084,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13084,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13084,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13084,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13084,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13084,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13084,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13084,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13084,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13084,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13084,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13084,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13084,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13084,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13084,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13084,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13084,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13084,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13084,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13084,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13084,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13084,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13084,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13084,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13084,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13084,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13084,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13084,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13084,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13084,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13084,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13084,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13084,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13084,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13084,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13084,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13084,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13084,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13084,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13084,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13084,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13084,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13084,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13084 : FrameRepair 13084 scalarRow13084 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13084Cells j).1 (repair13084Cells j).2.1
  endpoint_upper := fun j => ((repair13084Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13084Cells j).2.2

theorem repair13085Cells (j : Fin 43) :
    0 ≤ (scalarRow13085.table (sourceIndex j)).upper ∧
    (scalarRow13085.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13085.table (sourceIndex j)).centre) /
      (scalarRow13085.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13085.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13085,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13085,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13085,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13085,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13085,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13085,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13085,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13085,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13085,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13085,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13085,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13085,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13085,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13085,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13085,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13085,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13085,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13085,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13085,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13085,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13085,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13085,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13085,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13085,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13085,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13085,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13085,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13085,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13085,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13085,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13085,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13085,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13085,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13085,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13085,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13085,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13085,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13085,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13085,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13085,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13085,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13085,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13085,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13085,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13085,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13085,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13085,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13085,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13085,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13085,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13085,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13085,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13085,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13085,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13085,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13085,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13085,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13085,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13085,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13085,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13085,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13085,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13085,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13085,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13085,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13085,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13085,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13085,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13085,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13085,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13085,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13085,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13085,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13085,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13085,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13085,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13085,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13085,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13085,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13085,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13085,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13085,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13085,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13085,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13085,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13085,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13085 : FrameRepair 13085 scalarRow13085 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13085Cells j).1 (repair13085Cells j).2.1
  endpoint_upper := fun j => ((repair13085Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13085Cells j).2.2

theorem repair13086Cells (j : Fin 43) :
    0 ≤ (scalarRow13086.table (sourceIndex j)).upper ∧
    (scalarRow13086.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13086.table (sourceIndex j)).centre) /
      (scalarRow13086.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13086.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13086,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13086,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13086,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13086,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13086,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13086,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13086,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13086,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13086,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13086,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13086,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13086,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13086,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13086,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13086,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13086,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13086,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13086,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13086,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13086,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13086,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13086,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13086,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13086,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13086,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13086,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13086,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13086,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13086,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13086,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13086,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13086,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13086,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13086,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13086,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13086,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13086,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13086,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13086,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13086,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13086,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13086,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13086,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13086,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13086,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13086,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13086,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13086,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13086,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13086,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13086,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13086,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13086,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13086,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13086,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13086,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13086,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13086,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13086,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13086,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13086,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13086,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13086,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13086,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13086,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13086,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13086,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13086,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13086,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13086,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13086,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13086,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13086,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13086,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13086,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13086,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13086,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13086,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13086,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13086,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13086,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13086,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13086,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13086,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13086,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13086,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13086 : FrameRepair 13086 scalarRow13086 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13086Cells j).1 (repair13086Cells j).2.1
  endpoint_upper := fun j => ((repair13086Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13086Cells j).2.2

theorem repair13087Cells (j : Fin 43) :
    0 ≤ (scalarRow13087.table (sourceIndex j)).upper ∧
    (scalarRow13087.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13087.table (sourceIndex j)).centre) /
      (scalarRow13087.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13087.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13087,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13087,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13087,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13087,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13087,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13087,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13087,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13087,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13087,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13087,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13087,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13087,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13087,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13087,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13087,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13087,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13087,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13087,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13087,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13087,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13087,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13087,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13087,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13087,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13087,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13087,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13087,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13087,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13087,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13087,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13087,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13087,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13087,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13087,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13087,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13087,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13087,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13087,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13087,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13087,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13087,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13087,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13087,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13087,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13087,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13087,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13087,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13087,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13087,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13087,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13087,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13087,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13087,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13087,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13087,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13087,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13087,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13087,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13087,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13087,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13087,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13087,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13087,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13087,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13087,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13087,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13087,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13087,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13087,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13087,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13087,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13087,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13087,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13087,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13087,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13087,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13087,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13087,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13087,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13087,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13087,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13087,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13087,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13087,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13087,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13087,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13087 : FrameRepair 13087 scalarRow13087 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13087Cells j).1 (repair13087Cells j).2.1
  endpoint_upper := fun j => ((repair13087Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13087Cells j).2.2

theorem repair13088Cells (j : Fin 43) :
    0 ≤ (scalarRow13088.table (sourceIndex j)).upper ∧
    (scalarRow13088.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13088.table (sourceIndex j)).centre) /
      (scalarRow13088.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13088.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13088,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13088,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13088,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13088,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13088,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13088,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13088,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13088,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13088,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13088,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13088,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13088,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13088,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13088,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13088,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13088,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13088,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13088,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13088,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13088,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13088,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13088,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13088,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13088,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13088,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13088,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13088,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13088,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13088,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13088,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13088,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13088,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13088,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13088,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13088,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13088,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13088,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13088,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13088,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13088,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13088,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13088,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13088,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13088,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13088,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13088,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13088,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13088,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13088,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13088,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13088,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13088,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13088,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13088,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13088,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13088,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13088,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13088,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13088,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13088,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13088,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13088,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13088,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13088,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13088,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13088,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13088,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13088,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13088,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13088,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13088,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13088,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13088,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13088,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13088,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13088,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13088,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13088,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13088,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13088,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13088,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13088,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13088,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13088,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13088,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13088,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13088 : FrameRepair 13088 scalarRow13088 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13088Cells j).1 (repair13088Cells j).2.1
  endpoint_upper := fun j => ((repair13088Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13088Cells j).2.2

theorem repair13089Cells (j : Fin 43) :
    0 ≤ (scalarRow13089.table (sourceIndex j)).upper ∧
    (scalarRow13089.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13089.table (sourceIndex j)).centre) /
      (scalarRow13089.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13089.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13089,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13089,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13089,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13089,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13089,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13089,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13089,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13089,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13089,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13089,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13089,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13089,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13089,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13089,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13089,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13089,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13089,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13089,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13089,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13089,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13089,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13089,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13089,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13089,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13089,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13089,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13089,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13089,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13089,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13089,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13089,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13089,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13089,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13089,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13089,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13089,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13089,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13089,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13089,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13089,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13089,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13089,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13089,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13089,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13089,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13089,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13089,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13089,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13089,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13089,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13089,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13089,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13089,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13089,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13089,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13089,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13089,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13089,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13089,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13089,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13089,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13089,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13089,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13089,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13089,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13089,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13089,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13089,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13089,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13089,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13089,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13089,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13089,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13089,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13089,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13089,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13089,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13089,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13089,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13089,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13089,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13089,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13089,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13089,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13089,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13089,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13089 : FrameRepair 13089 scalarRow13089 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13089Cells j).1 (repair13089Cells j).2.1
  endpoint_upper := fun j => ((repair13089Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13089Cells j).2.2

theorem repair13090Cells (j : Fin 43) :
    0 ≤ (scalarRow13090.table (sourceIndex j)).upper ∧
    (scalarRow13090.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13090.table (sourceIndex j)).centre) /
      (scalarRow13090.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13090.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13090,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13090,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13090,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13090,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13090,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13090,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13090,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13090,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13090,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13090,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13090,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13090,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13090,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13090,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13090,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13090,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13090,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13090,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13090,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13090,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13090,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13090,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13090,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13090,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13090,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13090,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13090,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13090,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13090,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13090,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13090,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13090,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13090,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13090,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13090,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13090,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13090,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13090,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13090,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13090,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13090,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13090,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13090,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13090,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13090,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13090,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13090,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13090,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13090,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13090,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13090,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13090,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13090,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13090,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13090,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13090,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13090,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13090,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13090,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13090,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13090,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13090,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13090,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13090,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13090,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13090,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13090,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13090,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13090,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13090,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13090,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13090,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13090,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13090,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13090,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13090,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13090,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13090,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13090,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13090,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13090,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13090,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13090,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13090,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13090,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13090,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13090 : FrameRepair 13090 scalarRow13090 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13090Cells j).1 (repair13090Cells j).2.1
  endpoint_upper := fun j => ((repair13090Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13090Cells j).2.2

theorem repair13091Cells (j : Fin 43) :
    0 ≤ (scalarRow13091.table (sourceIndex j)).upper ∧
    (scalarRow13091.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13091.table (sourceIndex j)).centre) /
      (scalarRow13091.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13091.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13091,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13091,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13091,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13091,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13091,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13091,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13091,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13091,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13091,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13091,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13091,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13091,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13091,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13091,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13091,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13091,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13091,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13091,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13091,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13091,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13091,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13091,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13091,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13091,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13091,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13091,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13091,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13091,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13091,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13091,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13091,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13091,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13091,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13091,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13091,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13091,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13091,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13091,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13091,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13091,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13091,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13091,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13091,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13091,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13091,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13091,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13091,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13091,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13091,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13091,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13091,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13091,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13091,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13091,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13091,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13091,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13091,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13091,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13091,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13091,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13091,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13091,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13091,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13091,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13091,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13091,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13091,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13091,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13091,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13091,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13091,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13091,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13091,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13091,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13091,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13091,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13091,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13091,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13091,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13091,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13091,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13091,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13091,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13091,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13091,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13091,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13091 : FrameRepair 13091 scalarRow13091 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13091Cells j).1 (repair13091Cells j).2.1
  endpoint_upper := fun j => ((repair13091Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13091Cells j).2.2

theorem repair13092Cells (j : Fin 43) :
    0 ≤ (scalarRow13092.table (sourceIndex j)).upper ∧
    (scalarRow13092.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13092.table (sourceIndex j)).centre) /
      (scalarRow13092.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13092.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13092,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13092,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13092,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13092,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13092,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13092,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13092,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13092,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13092,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13092,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13092,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13092,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13092,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13092,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13092,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13092,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13092,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13092,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13092,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13092,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13092,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13092,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13092,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13092,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13092,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13092,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13092,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13092,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13092,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13092,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13092,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13092,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13092,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13092,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13092,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13092,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13092,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13092,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13092,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13092,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13092,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13092,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13092,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13092,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13092,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13092,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13092,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13092,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13092,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13092,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13092,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13092,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13092,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13092,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13092,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13092,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13092,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13092,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13092,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13092,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13092,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13092,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13092,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13092,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13092,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13092,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13092,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13092,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13092,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13092,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13092,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13092,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13092,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13092,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13092,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13092,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13092,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13092,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13092,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13092,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13092,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13092,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13092,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13092,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13092,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13092,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13092 : FrameRepair 13092 scalarRow13092 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13092Cells j).1 (repair13092Cells j).2.1
  endpoint_upper := fun j => ((repair13092Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13092Cells j).2.2

theorem repair13093Cells (j : Fin 43) :
    0 ≤ (scalarRow13093.table (sourceIndex j)).upper ∧
    (scalarRow13093.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13093.table (sourceIndex j)).centre) /
      (scalarRow13093.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13093.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13093,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13093,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13093,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13093,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13093,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13093,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13093,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13093,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13093,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13093,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13093,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13093,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13093,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13093,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13093,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13093,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13093,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13093,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13093,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13093,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13093,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13093,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13093,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13093,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13093,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13093,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13093,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13093,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13093,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13093,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13093,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13093,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13093,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13093,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13093,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13093,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13093,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13093,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13093,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13093,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13093,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13093,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13093,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13093,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13093,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13093,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13093,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13093,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13093,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13093,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13093,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13093,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13093,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13093,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13093,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13093,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13093,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13093,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13093,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13093,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13093,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13093,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13093,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13093,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13093,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13093,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13093,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13093,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13093,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13093,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13093,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13093,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13093,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13093,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13093,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13093,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13093,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13093,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13093,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13093,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13093,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13093,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13093,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13093,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13093,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13093,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13093 : FrameRepair 13093 scalarRow13093 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13093Cells j).1 (repair13093Cells j).2.1
  endpoint_upper := fun j => ((repair13093Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13093Cells j).2.2

theorem repair13094Cells (j : Fin 43) :
    0 ≤ (scalarRow13094.table (sourceIndex j)).upper ∧
    (scalarRow13094.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13094.table (sourceIndex j)).centre) /
      (scalarRow13094.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13094.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13094,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13094,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13094,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13094,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13094,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13094,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13094,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13094,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13094,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13094,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13094,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13094,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13094,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13094,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13094,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13094,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13094,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13094,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13094,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13094,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13094,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13094,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13094,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13094,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13094,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13094,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13094,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13094,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13094,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13094,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13094,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13094,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13094,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13094,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13094,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13094,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13094,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13094,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13094,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13094,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13094,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13094,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13094,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13094,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13094,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13094,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13094,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13094,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13094,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13094,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13094,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13094,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13094,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13094,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13094,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13094,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13094,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13094,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13094,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13094,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13094,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13094,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13094,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13094,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13094,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13094,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13094,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13094,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13094,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13094,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13094,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13094,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13094,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13094,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13094,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13094,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13094,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13094,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13094,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13094,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13094,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13094,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13094,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13094,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13094,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13094,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13094 : FrameRepair 13094 scalarRow13094 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13094Cells j).1 (repair13094Cells j).2.1
  endpoint_upper := fun j => ((repair13094Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13094Cells j).2.2

theorem repair13095Cells (j : Fin 43) :
    0 ≤ (scalarRow13095.table (sourceIndex j)).upper ∧
    (scalarRow13095.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13095.table (sourceIndex j)).centre) /
      (scalarRow13095.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13095.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13095,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13095,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13095,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13095,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13095,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13095,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13095,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13095,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13095,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13095,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13095,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13095,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13095,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13095,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13095,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13095,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13095,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13095,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13095,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13095,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13095,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13095,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13095,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13095,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13095,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13095,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13095,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13095,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13095,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13095,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13095,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13095,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13095,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13095,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13095,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13095,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13095,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13095,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13095,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13095,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13095,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13095,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13095,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13095,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13095,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13095,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13095,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13095,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13095,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13095,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13095,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13095,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13095,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13095,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13095,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13095,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13095,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13095,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13095,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13095,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13095,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13095,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13095,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13095,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13095,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13095,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13095,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13095,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13095,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13095,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13095,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13095,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13095,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13095,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13095,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13095,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13095,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13095,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13095,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13095,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13095,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13095,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13095,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13095,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13095,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13095,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13095 : FrameRepair 13095 scalarRow13095 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13095Cells j).1 (repair13095Cells j).2.1
  endpoint_upper := fun j => ((repair13095Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13095Cells j).2.2

theorem repair13096Cells (j : Fin 43) :
    0 ≤ (scalarRow13096.table (sourceIndex j)).upper ∧
    (scalarRow13096.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13096.table (sourceIndex j)).centre) /
      (scalarRow13096.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13096.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13096,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13096,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13096,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13096,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13096,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13096,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13096,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13096,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13096,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13096,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13096,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13096,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13096,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13096,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13096,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13096,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13096,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13096,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13096,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13096,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13096,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13096,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13096,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13096,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13096,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13096,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13096,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13096,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13096,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13096,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13096,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13096,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13096,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13096,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13096,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13096,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13096,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13096,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13096,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13096,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13096,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13096,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13096,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13096,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13096,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13096,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13096,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13096,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13096,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13096,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13096,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13096,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13096,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13096,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13096,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13096,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13096,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13096,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13096,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13096,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13096,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13096,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13096,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13096,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13096,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13096,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13096,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13096,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13096,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13096,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13096,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13096,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13096,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13096,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13096,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13096,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13096,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13096,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13096,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13096,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13096,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13096,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13096,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13096,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13096,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13096,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13096 : FrameRepair 13096 scalarRow13096 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13096Cells j).1 (repair13096Cells j).2.1
  endpoint_upper := fun j => ((repair13096Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13096Cells j).2.2

theorem repair13097Cells (j : Fin 43) :
    0 ≤ (scalarRow13097.table (sourceIndex j)).upper ∧
    (scalarRow13097.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13097.table (sourceIndex j)).centre) /
      (scalarRow13097.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13097.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13097,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13097,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13097,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13097,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13097,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13097,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13097,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13097,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13097,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13097,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13097,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13097,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13097,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13097,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13097,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13097,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13097,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13097,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13097,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13097,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13097,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13097,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13097,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13097,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13097,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13097,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13097,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13097,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13097,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13097,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13097,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13097,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13097,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13097,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13097,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13097,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13097,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13097,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13097,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13097,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13097,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13097,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13097,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13097,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13097,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13097,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13097,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13097,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13097,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13097,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13097,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13097,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13097,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13097,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13097,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13097,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13097,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13097,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13097,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13097,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13097,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13097,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13097,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13097,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13097,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13097,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13097,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13097,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13097,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13097,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13097,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13097,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13097,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13097,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13097,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13097,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13097,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13097,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13097,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13097,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13097,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13097,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13097,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13097,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13097,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13097,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13097 : FrameRepair 13097 scalarRow13097 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13097Cells j).1 (repair13097Cells j).2.1
  endpoint_upper := fun j => ((repair13097Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13097Cells j).2.2

theorem repair13098Cells (j : Fin 43) :
    0 ≤ (scalarRow13098.table (sourceIndex j)).upper ∧
    (scalarRow13098.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13098.table (sourceIndex j)).centre) /
      (scalarRow13098.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13098.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13098,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13098,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13098,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13098,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13098,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13098,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13098,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13098,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13098,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13098,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13098,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13098,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13098,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13098,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13098,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13098,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13098,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13098,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13098,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13098,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13098,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13098,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13098,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13098,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13098,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13098,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13098,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13098,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13098,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13098,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13098,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13098,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13098,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13098,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13098,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13098,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13098,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13098,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13098,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13098,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13098,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13098,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13098,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13098,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13098,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13098,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13098,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13098,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13098,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13098,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13098,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13098,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13098,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13098,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13098,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13098,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13098,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13098,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13098,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13098,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13098,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13098,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13098,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13098,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13098,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13098,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13098,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13098,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13098,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13098,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13098,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13098,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13098,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13098,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13098,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13098,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13098,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13098,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13098,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13098,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13098,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13098,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13098,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13098,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13098,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13098,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13098 : FrameRepair 13098 scalarRow13098 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13098Cells j).1 (repair13098Cells j).2.1
  endpoint_upper := fun j => ((repair13098Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13098Cells j).2.2

theorem repair13099Cells (j : Fin 43) :
    0 ≤ (scalarRow13099.table (sourceIndex j)).upper ∧
    (scalarRow13099.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13099.table (sourceIndex j)).centre) /
      (scalarRow13099.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13099.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13099,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13099,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13099,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13099,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13099,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13099,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13099,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13099,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13099,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13099,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13099,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13099,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13099,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13099,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13099,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13099,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13099,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13099,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13099,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13099,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13099,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13099,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13099,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13099,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13099,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13099,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13099,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13099,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13099,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13099,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13099,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13099,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13099,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13099,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13099,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13099,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13099,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13099,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13099,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13099,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13099,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13099,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13099,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13099,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13099,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13099,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13099,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13099,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13099,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13099,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13099,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13099,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13099,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13099,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13099,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13099,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13099,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13099,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13099,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13099,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13099,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13099,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13099,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13099,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13099,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13099,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13099,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13099,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13099,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13099,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13099,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13099,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13099,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13099,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13099,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13099,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13099,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13099,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13099,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13099,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13099,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13099,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13099,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13099,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13099,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13099,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13099 : FrameRepair 13099 scalarRow13099 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13099Cells j).1 (repair13099Cells j).2.1
  endpoint_upper := fun j => ((repair13099Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13099Cells j).2.2

end BstLean.Part269
