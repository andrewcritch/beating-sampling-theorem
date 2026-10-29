import BstLean.Part269Rows31
import BstLean.Part269RepairCommon
namespace BstLean.Part269
open Real Set BstLean.Part255 BstLean.Part263 BstLean.Part264
theorem repair13125Cells (j : Fin 43) :
    0 ≤ (scalarRow13125.table (sourceIndex j)).upper ∧
    (scalarRow13125.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13125.table (sourceIndex j)).centre) /
      (scalarRow13125.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13125.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13125,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13125,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13125,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13125,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13125,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13125,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13125,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13125,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13125,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13125,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13125,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13125,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13125,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13125,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13125,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13125,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13125,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13125,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13125,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13125,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13125,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13125,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13125,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13125,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13125,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13125,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13125,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13125,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13125,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13125,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13125,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13125,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13125,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13125,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13125,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13125,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13125,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13125,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13125,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13125,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13125,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13125,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13125,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13125,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13125,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13125,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13125,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13125,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13125,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13125,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13125,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13125,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13125,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13125,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13125,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13125,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13125,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13125,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13125,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13125,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13125,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13125,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13125,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13125,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13125,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13125,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13125,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13125,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13125,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13125,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13125,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13125,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13125,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13125,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13125,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13125,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13125,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13125,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13125,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13125,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13125,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13125,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13125,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13125,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13125,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13125,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13125 : FrameRepair 13125 scalarRow13125 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13125Cells j).1 (repair13125Cells j).2.1
  endpoint_upper := fun j => ((repair13125Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13125Cells j).2.2

theorem repair13126Cells (j : Fin 43) :
    0 ≤ (scalarRow13126.table (sourceIndex j)).upper ∧
    (scalarRow13126.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13126.table (sourceIndex j)).centre) /
      (scalarRow13126.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13126.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13126,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13126,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13126,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13126,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13126,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13126,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13126,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13126,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13126,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13126,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13126,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13126,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13126,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13126,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13126,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13126,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13126,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13126,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13126,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13126,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13126,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13126,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13126,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13126,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13126,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13126,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13126,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13126,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13126,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13126,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13126,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13126,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13126,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13126,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13126,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13126,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13126,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13126,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13126,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13126,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13126,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13126,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13126,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13126,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13126,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13126,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13126,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13126,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13126,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13126,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13126,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13126,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13126,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13126,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13126,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13126,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13126,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13126,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13126,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13126,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13126,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13126,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13126,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13126,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13126,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13126,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13126,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13126,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13126,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13126,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13126,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13126,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13126,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13126,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13126,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13126,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13126,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13126,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13126,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13126,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13126,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13126,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13126,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13126,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13126,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13126,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13126 : FrameRepair 13126 scalarRow13126 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13126Cells j).1 (repair13126Cells j).2.1
  endpoint_upper := fun j => ((repair13126Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13126Cells j).2.2

theorem repair13127Cells (j : Fin 43) :
    0 ≤ (scalarRow13127.table (sourceIndex j)).upper ∧
    (scalarRow13127.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13127.table (sourceIndex j)).centre) /
      (scalarRow13127.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13127.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13127,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13127,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13127,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13127,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13127,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13127,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13127,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13127,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13127,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13127,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13127,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13127,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13127,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13127,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13127,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13127,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13127,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13127,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13127,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13127,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13127,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13127,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13127,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13127,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13127,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13127,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13127,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13127,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13127,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13127,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13127,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13127,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13127,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13127,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13127,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13127,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13127,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13127,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13127,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13127,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13127,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13127,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13127,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13127,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13127,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13127,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13127,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13127,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13127,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13127,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13127,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13127,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13127,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13127,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13127,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13127,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13127,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13127,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13127,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13127,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13127,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13127,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13127,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13127,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13127,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13127,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13127,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13127,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13127,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13127,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13127,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13127,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13127,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13127,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13127,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13127,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13127,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13127,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13127,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13127,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13127,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13127,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13127,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13127,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13127,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13127,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13127 : FrameRepair 13127 scalarRow13127 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13127Cells j).1 (repair13127Cells j).2.1
  endpoint_upper := fun j => ((repair13127Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13127Cells j).2.2

theorem repair13128Cells (j : Fin 43) :
    0 ≤ (scalarRow13128.table (sourceIndex j)).upper ∧
    (scalarRow13128.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13128.table (sourceIndex j)).centre) /
      (scalarRow13128.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13128.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13128,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13128,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13128,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13128,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13128,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13128,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13128,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13128,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13128,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13128,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13128,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13128,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13128,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13128,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13128,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13128,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13128,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13128,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13128,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13128,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13128,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13128,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13128,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13128,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13128,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13128,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13128,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13128,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13128,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13128,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13128,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13128,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13128,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13128,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13128,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13128,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13128,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13128,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13128,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13128,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13128,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13128,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13128,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13128,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13128,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13128,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13128,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13128,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13128,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13128,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13128,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13128,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13128,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13128,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13128,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13128,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13128,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13128,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13128,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13128,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13128,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13128,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13128,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13128,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13128,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13128,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13128,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13128,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13128,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13128,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13128,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13128,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13128,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13128,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13128,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13128,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13128,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13128,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13128,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13128,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13128,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13128,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13128,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13128,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13128,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13128,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13128 : FrameRepair 13128 scalarRow13128 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13128Cells j).1 (repair13128Cells j).2.1
  endpoint_upper := fun j => ((repair13128Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13128Cells j).2.2

theorem repair13129Cells (j : Fin 43) :
    0 ≤ (scalarRow13129.table (sourceIndex j)).upper ∧
    (scalarRow13129.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13129.table (sourceIndex j)).centre) /
      (scalarRow13129.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13129.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13129,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13129,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13129,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13129,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13129,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13129,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13129,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13129,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13129,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13129,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13129,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13129,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13129,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13129,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13129,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13129,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13129,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13129,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13129,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13129,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13129,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13129,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13129,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13129,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13129,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13129,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13129,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13129,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13129,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13129,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13129,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13129,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13129,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13129,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13129,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13129,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13129,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13129,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13129,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13129,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13129,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13129,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13129,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13129,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13129,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13129,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13129,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13129,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13129,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13129,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13129,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13129,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13129,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13129,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13129,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13129,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13129,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13129,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13129,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13129,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13129,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13129,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13129,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13129,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13129,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13129,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13129,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13129,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13129,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13129,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13129,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13129,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13129,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13129,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13129,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13129,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13129,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13129,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13129,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13129,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13129,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13129,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13129,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13129,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13129,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13129,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13129 : FrameRepair 13129 scalarRow13129 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13129Cells j).1 (repair13129Cells j).2.1
  endpoint_upper := fun j => ((repair13129Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13129Cells j).2.2

theorem repair13130Cells (j : Fin 43) :
    0 ≤ (scalarRow13130.table (sourceIndex j)).upper ∧
    (scalarRow13130.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13130.table (sourceIndex j)).centre) /
      (scalarRow13130.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13130.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13130,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13130,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13130,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13130,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13130,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13130,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13130,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13130,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13130,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13130,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13130,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13130,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13130,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13130,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13130,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13130,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13130,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13130,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13130,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13130,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13130,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13130,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13130,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13130,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13130,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13130,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13130,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13130,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13130,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13130,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13130,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13130,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13130,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13130,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13130,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13130,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13130,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13130,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13130,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13130,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13130,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13130,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13130,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13130,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13130,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13130,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13130,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13130,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13130,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13130,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13130,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13130,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13130,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13130,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13130,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13130,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13130,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13130,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13130,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13130,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13130,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13130,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13130,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13130,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13130,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13130,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13130,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13130,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13130,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13130,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13130,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13130,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13130,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13130,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13130,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13130,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13130,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13130,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13130,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13130,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13130,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13130,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13130,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13130,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13130,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13130,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13130 : FrameRepair 13130 scalarRow13130 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13130Cells j).1 (repair13130Cells j).2.1
  endpoint_upper := fun j => ((repair13130Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13130Cells j).2.2

theorem repair13131Cells (j : Fin 43) :
    0 ≤ (scalarRow13131.table (sourceIndex j)).upper ∧
    (scalarRow13131.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13131.table (sourceIndex j)).centre) /
      (scalarRow13131.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13131.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13131,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13131,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13131,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13131,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13131,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13131,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13131,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13131,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13131,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13131,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13131,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13131,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13131,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13131,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13131,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13131,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13131,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13131,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13131,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13131,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13131,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13131,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13131,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13131,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13131,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13131,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13131,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13131,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13131,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13131,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13131,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13131,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13131,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13131,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13131,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13131,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13131,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13131,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13131,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13131,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13131,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13131,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13131,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13131,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13131,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13131,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13131,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13131,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13131,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13131,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13131,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13131,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13131,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13131,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13131,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13131,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13131,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13131,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13131,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13131,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13131,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13131,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13131,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13131,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13131,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13131,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13131,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13131,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13131,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13131,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13131,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13131,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13131,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13131,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13131,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13131,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13131,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13131,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13131,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13131,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13131,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13131,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13131,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13131,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13131,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13131,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13131 : FrameRepair 13131 scalarRow13131 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13131Cells j).1 (repair13131Cells j).2.1
  endpoint_upper := fun j => ((repair13131Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13131Cells j).2.2

theorem repair13132Cells (j : Fin 43) :
    0 ≤ (scalarRow13132.table (sourceIndex j)).upper ∧
    (scalarRow13132.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13132.table (sourceIndex j)).centre) /
      (scalarRow13132.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13132.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13132,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13132,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13132,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13132,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13132,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13132,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13132,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13132,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13132,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13132,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13132,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13132,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13132,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13132,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13132,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13132,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13132,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13132,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13132,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13132,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13132,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13132,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13132,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13132,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13132,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13132,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13132,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13132,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13132,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13132,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13132,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13132,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13132,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13132,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13132,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13132,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13132,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13132,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13132,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13132,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13132,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13132,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13132,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13132,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13132,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13132,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13132,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13132,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13132,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13132,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13132,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13132,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13132,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13132,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13132,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13132,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13132,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13132,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13132,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13132,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13132,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13132,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13132,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13132,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13132,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13132,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13132,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13132,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13132,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13132,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13132,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13132,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13132,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13132,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13132,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13132,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13132,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13132,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13132,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13132,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13132,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13132,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13132,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13132,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13132,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13132,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13132 : FrameRepair 13132 scalarRow13132 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13132Cells j).1 (repair13132Cells j).2.1
  endpoint_upper := fun j => ((repair13132Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13132Cells j).2.2

theorem repair13133Cells (j : Fin 43) :
    0 ≤ (scalarRow13133.table (sourceIndex j)).upper ∧
    (scalarRow13133.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13133.table (sourceIndex j)).centre) /
      (scalarRow13133.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13133.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13133,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13133,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13133,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13133,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13133,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13133,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13133,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13133,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13133,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13133,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13133,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13133,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13133,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13133,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13133,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13133,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13133,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13133,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13133,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13133,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13133,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13133,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13133,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13133,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13133,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13133,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13133,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13133,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13133,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13133,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13133,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13133,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13133,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13133,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13133,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13133,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13133,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13133,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13133,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13133,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13133,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13133,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13133,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13133,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13133,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13133,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13133,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13133,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13133,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13133,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13133,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13133,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13133,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13133,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13133,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13133,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13133,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13133,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13133,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13133,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13133,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13133,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13133,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13133,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13133,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13133,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13133,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13133,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13133,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13133,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13133,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13133,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13133,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13133,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13133,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13133,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13133,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13133,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13133,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13133,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13133,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13133,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13133,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13133,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13133,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13133,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13133 : FrameRepair 13133 scalarRow13133 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13133Cells j).1 (repair13133Cells j).2.1
  endpoint_upper := fun j => ((repair13133Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13133Cells j).2.2

theorem repair13134Cells (j : Fin 43) :
    0 ≤ (scalarRow13134.table (sourceIndex j)).upper ∧
    (scalarRow13134.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13134.table (sourceIndex j)).centre) /
      (scalarRow13134.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13134.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13134,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13134,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13134,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13134,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13134,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13134,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13134,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13134,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13134,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13134,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13134,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13134,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13134,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13134,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13134,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13134,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13134,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13134,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13134,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13134,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13134,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13134,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13134,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13134,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13134,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13134,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13134,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13134,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13134,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13134,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13134,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13134,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13134,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13134,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13134,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13134,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13134,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13134,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13134,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13134,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13134,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13134,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13134,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13134,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13134,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13134,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13134,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13134,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13134,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13134,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13134,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13134,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13134,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13134,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13134,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13134,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13134,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13134,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13134,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13134,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13134,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13134,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13134,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13134,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13134,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13134,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13134,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13134,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13134,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13134,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13134,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13134,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13134,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13134,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13134,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13134,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13134,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13134,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13134,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13134,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13134,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13134,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13134,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13134,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13134,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13134,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13134 : FrameRepair 13134 scalarRow13134 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13134Cells j).1 (repair13134Cells j).2.1
  endpoint_upper := fun j => ((repair13134Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13134Cells j).2.2

theorem repair13135Cells (j : Fin 43) :
    0 ≤ (scalarRow13135.table (sourceIndex j)).upper ∧
    (scalarRow13135.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13135.table (sourceIndex j)).centre) /
      (scalarRow13135.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13135.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13135,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13135,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13135,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13135,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13135,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13135,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13135,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13135,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13135,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13135,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13135,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13135,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13135,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13135,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13135,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13135,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13135,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13135,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13135,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13135,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13135,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13135,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13135,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13135,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13135,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13135,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13135,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13135,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13135,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13135,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13135,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13135,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13135,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13135,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13135,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13135,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13135,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13135,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13135,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13135,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13135,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13135,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13135,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13135,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13135,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13135,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13135,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13135,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13135,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13135,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13135,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13135,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13135,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13135,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13135,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13135,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13135,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13135,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13135,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13135,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13135,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13135,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13135,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13135,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13135,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13135,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13135,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13135,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13135,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13135,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13135,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13135,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13135,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13135,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13135,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13135,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13135,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13135,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13135,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13135,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13135,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13135,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13135,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13135,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13135,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13135,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13135 : FrameRepair 13135 scalarRow13135 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13135Cells j).1 (repair13135Cells j).2.1
  endpoint_upper := fun j => ((repair13135Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13135Cells j).2.2

theorem repair13136Cells (j : Fin 43) :
    0 ≤ (scalarRow13136.table (sourceIndex j)).upper ∧
    (scalarRow13136.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13136.table (sourceIndex j)).centre) /
      (scalarRow13136.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13136.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13136,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13136,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13136,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13136,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13136,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13136,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13136,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13136,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13136,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13136,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13136,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13136,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13136,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13136,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13136,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13136,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13136,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13136,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13136,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13136,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13136,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13136,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13136,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13136,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13136,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13136,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13136,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13136,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13136,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13136,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13136,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13136,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13136,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13136,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13136,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13136,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13136,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13136,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13136,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13136,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13136,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13136,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13136,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13136,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13136,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13136,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13136,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13136,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13136,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13136,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13136,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13136,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13136,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13136,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13136,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13136,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13136,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13136,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13136,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13136,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13136,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13136,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13136,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13136,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13136,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13136,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13136,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13136,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13136,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13136,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13136,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13136,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13136,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13136,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13136,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13136,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13136,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13136,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13136,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13136,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13136,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13136,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13136,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13136,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13136,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13136,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13136 : FrameRepair 13136 scalarRow13136 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13136Cells j).1 (repair13136Cells j).2.1
  endpoint_upper := fun j => ((repair13136Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13136Cells j).2.2

theorem repair13137Cells (j : Fin 43) :
    0 ≤ (scalarRow13137.table (sourceIndex j)).upper ∧
    (scalarRow13137.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13137.table (sourceIndex j)).centre) /
      (scalarRow13137.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13137.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13137,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13137,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13137,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13137,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13137,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13137,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13137,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13137,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13137,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13137,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13137,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13137,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13137,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13137,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13137,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13137,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13137,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13137,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13137,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13137,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13137,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13137,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13137,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13137,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13137,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13137,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13137,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13137,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13137,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13137,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13137,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13137,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13137,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13137,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13137,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13137,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13137,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13137,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13137,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13137,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13137,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13137,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13137,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13137,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13137,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13137,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13137,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13137,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13137,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13137,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13137,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13137,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13137,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13137,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13137,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13137,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13137,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13137,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13137,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13137,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13137,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13137,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13137,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13137,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13137,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13137,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13137,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13137,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13137,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13137,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13137,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13137,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13137,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13137,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13137,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13137,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13137,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13137,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13137,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13137,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13137,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13137,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13137,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13137,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13137,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13137,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13137 : FrameRepair 13137 scalarRow13137 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13137Cells j).1 (repair13137Cells j).2.1
  endpoint_upper := fun j => ((repair13137Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13137Cells j).2.2

theorem repair13138Cells (j : Fin 43) :
    0 ≤ (scalarRow13138.table (sourceIndex j)).upper ∧
    (scalarRow13138.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13138.table (sourceIndex j)).centre) /
      (scalarRow13138.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13138.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13138,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13138,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13138,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13138,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13138,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13138,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13138,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13138,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13138,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13138,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13138,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13138,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13138,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13138,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13138,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13138,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13138,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13138,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13138,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13138,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13138,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13138,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13138,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13138,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13138,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13138,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13138,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13138,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13138,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13138,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13138,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13138,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13138,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13138,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13138,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13138,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13138,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13138,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13138,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13138,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13138,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13138,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13138,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13138,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13138,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13138,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13138,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13138,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13138,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13138,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13138,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13138,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13138,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13138,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13138,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13138,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13138,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13138,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13138,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13138,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13138,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13138,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13138,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13138,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13138,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13138,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13138,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13138,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13138,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13138,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13138,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13138,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13138,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13138,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13138,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13138,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13138,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13138,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13138,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13138,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13138,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13138,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13138,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13138,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13138,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13138,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13138 : FrameRepair 13138 scalarRow13138 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13138Cells j).1 (repair13138Cells j).2.1
  endpoint_upper := fun j => ((repair13138Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13138Cells j).2.2

theorem repair13139Cells (j : Fin 43) :
    0 ≤ (scalarRow13139.table (sourceIndex j)).upper ∧
    (scalarRow13139.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13139.table (sourceIndex j)).centre) /
      (scalarRow13139.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13139.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13139,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13139,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13139,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13139,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13139,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13139,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13139,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13139,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13139,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13139,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13139,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13139,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13139,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13139,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13139,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13139,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13139,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13139,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13139,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13139,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13139,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13139,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13139,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13139,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13139,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13139,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13139,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13139,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13139,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13139,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13139,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13139,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13139,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13139,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13139,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13139,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13139,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13139,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13139,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13139,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13139,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13139,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13139,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13139,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13139,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13139,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13139,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13139,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13139,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13139,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13139,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13139,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13139,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13139,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13139,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13139,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13139,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13139,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13139,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13139,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13139,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13139,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13139,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13139,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13139,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13139,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13139,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13139,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13139,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13139,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13139,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13139,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13139,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13139,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13139,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13139,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13139,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13139,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13139,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13139,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13139,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13139,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13139,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13139,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13139,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13139,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13139 : FrameRepair 13139 scalarRow13139 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13139Cells j).1 (repair13139Cells j).2.1
  endpoint_upper := fun j => ((repair13139Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13139Cells j).2.2

theorem repair13140Cells (j : Fin 43) :
    0 ≤ (scalarRow13140.table (sourceIndex j)).upper ∧
    (scalarRow13140.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13140.table (sourceIndex j)).centre) /
      (scalarRow13140.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13140.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13140,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13140,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13140,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13140,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13140,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13140,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13140,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13140,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13140,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13140,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13140,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13140,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13140,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13140,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13140,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13140,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13140,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13140,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13140,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13140,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13140,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13140,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13140,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13140,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13140,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13140,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13140,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13140,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13140,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13140,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13140,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13140,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13140,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13140,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13140,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13140,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13140,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13140,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13140,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13140,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13140,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13140,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13140,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13140,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13140,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13140,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13140,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13140,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13140,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13140,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13140,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13140,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13140,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13140,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13140,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13140,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13140,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13140,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13140,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13140,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13140,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13140,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13140,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13140,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13140,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13140,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13140,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13140,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13140,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13140,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13140,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13140,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13140,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13140,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13140,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13140,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13140,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13140,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13140,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13140,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13140,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13140,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13140,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13140,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13140,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13140,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13140 : FrameRepair 13140 scalarRow13140 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13140Cells j).1 (repair13140Cells j).2.1
  endpoint_upper := fun j => ((repair13140Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13140Cells j).2.2

theorem repair13141Cells (j : Fin 43) :
    0 ≤ (scalarRow13141.table (sourceIndex j)).upper ∧
    (scalarRow13141.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13141.table (sourceIndex j)).centre) /
      (scalarRow13141.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13141.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13141,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13141,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13141,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13141,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13141,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13141,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13141,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13141,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13141,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13141,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13141,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13141,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13141,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13141,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13141,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13141,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13141,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13141,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13141,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13141,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13141,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13141,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13141,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13141,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13141,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13141,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13141,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13141,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13141,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13141,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13141,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13141,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13141,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13141,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13141,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13141,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13141,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13141,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13141,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13141,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13141,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13141,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13141,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13141,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13141,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13141,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13141,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13141,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13141,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13141,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13141,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13141,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13141,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13141,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13141,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13141,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13141,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13141,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13141,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13141,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13141,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13141,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13141,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13141,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13141,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13141,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13141,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13141,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13141,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13141,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13141,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13141,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13141,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13141,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13141,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13141,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13141,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13141,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13141,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13141,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13141,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13141,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13141,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13141,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13141,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13141,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13141 : FrameRepair 13141 scalarRow13141 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13141Cells j).1 (repair13141Cells j).2.1
  endpoint_upper := fun j => ((repair13141Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13141Cells j).2.2

theorem repair13142Cells (j : Fin 43) :
    0 ≤ (scalarRow13142.table (sourceIndex j)).upper ∧
    (scalarRow13142.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13142.table (sourceIndex j)).centre) /
      (scalarRow13142.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13142.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13142,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13142,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13142,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13142,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13142,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13142,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13142,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13142,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13142,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13142,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13142,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13142,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13142,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13142,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13142,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13142,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13142,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13142,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13142,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13142,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13142,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13142,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13142,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13142,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13142,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13142,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13142,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13142,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13142,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13142,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13142,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13142,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13142,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13142,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13142,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13142,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13142,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13142,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13142,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13142,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13142,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13142,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13142,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13142,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13142,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13142,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13142,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13142,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13142,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13142,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13142,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13142,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13142,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13142,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13142,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13142,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13142,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13142,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13142,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13142,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13142,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13142,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13142,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13142,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13142,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13142,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13142,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13142,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13142,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13142,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13142,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13142,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13142,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13142,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13142,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13142,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13142,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13142,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13142,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13142,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13142,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13142,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13142,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13142,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13142,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13142,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13142 : FrameRepair 13142 scalarRow13142 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13142Cells j).1 (repair13142Cells j).2.1
  endpoint_upper := fun j => ((repair13142Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13142Cells j).2.2

theorem repair13143Cells (j : Fin 43) :
    0 ≤ (scalarRow13143.table (sourceIndex j)).upper ∧
    (scalarRow13143.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13143.table (sourceIndex j)).centre) /
      (scalarRow13143.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13143.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13143,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13143,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13143,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13143,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13143,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13143,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13143,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13143,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13143,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13143,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13143,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13143,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13143,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13143,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13143,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13143,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13143,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13143,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13143,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13143,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13143,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13143,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13143,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13143,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13143,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13143,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13143,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13143,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13143,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13143,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13143,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13143,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13143,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13143,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13143,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13143,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13143,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13143,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13143,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13143,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13143,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13143,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13143,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13143,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13143,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13143,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13143,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13143,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13143,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13143,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13143,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13143,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13143,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13143,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13143,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13143,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13143,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13143,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13143,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13143,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13143,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13143,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13143,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13143,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13143,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13143,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13143,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13143,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13143,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13143,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13143,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13143,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13143,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13143,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13143,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13143,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13143,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13143,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13143,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13143,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13143,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13143,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13143,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13143,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13143,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13143,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13143 : FrameRepair 13143 scalarRow13143 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13143Cells j).1 (repair13143Cells j).2.1
  endpoint_upper := fun j => ((repair13143Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13143Cells j).2.2

theorem repair13144Cells (j : Fin 43) :
    0 ≤ (scalarRow13144.table (sourceIndex j)).upper ∧
    (scalarRow13144.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13144.table (sourceIndex j)).centre) /
      (scalarRow13144.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13144.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13144,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13144,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13144,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13144,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13144,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13144,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13144,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13144,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13144,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13144,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13144,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13144,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13144,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13144,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13144,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13144,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13144,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13144,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13144,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13144,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13144,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13144,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13144,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13144,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13144,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13144,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13144,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13144,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13144,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13144,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13144,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13144,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13144,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13144,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13144,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13144,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13144,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13144,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13144,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13144,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13144,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13144,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13144,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13144,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13144,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13144,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13144,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13144,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13144,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13144,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13144,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13144,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13144,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13144,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13144,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13144,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13144,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13144,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13144,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13144,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13144,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13144,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13144,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13144,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13144,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13144,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13144,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13144,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13144,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13144,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13144,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13144,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13144,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13144,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13144,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13144,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13144,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13144,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13144,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13144,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13144,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13144,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13144,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13144,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13144,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13144,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13144 : FrameRepair 13144 scalarRow13144 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13144Cells j).1 (repair13144Cells j).2.1
  endpoint_upper := fun j => ((repair13144Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13144Cells j).2.2

theorem repair13145Cells (j : Fin 43) :
    0 ≤ (scalarRow13145.table (sourceIndex j)).upper ∧
    (scalarRow13145.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13145.table (sourceIndex j)).centre) /
      (scalarRow13145.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13145.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13145,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13145,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13145,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13145,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13145,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13145,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13145,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13145,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13145,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13145,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13145,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13145,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13145,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13145,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13145,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13145,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13145,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13145,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13145,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13145,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13145,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13145,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13145,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13145,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13145,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13145,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13145,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13145,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13145,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13145,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13145,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13145,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13145,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13145,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13145,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13145,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13145,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13145,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13145,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13145,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13145,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13145,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13145,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13145,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13145,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13145,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13145,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13145,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13145,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13145,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13145,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13145,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13145,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13145,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13145,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13145,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13145,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13145,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13145,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13145,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13145,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13145,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13145,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13145,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13145,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13145,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13145,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13145,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13145,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13145,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13145,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13145,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13145,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13145,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13145,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13145,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13145,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13145,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13145,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13145,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13145,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13145,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13145,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13145,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13145,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13145,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13145 : FrameRepair 13145 scalarRow13145 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13145Cells j).1 (repair13145Cells j).2.1
  endpoint_upper := fun j => ((repair13145Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13145Cells j).2.2

theorem repair13146Cells (j : Fin 43) :
    0 ≤ (scalarRow13146.table (sourceIndex j)).upper ∧
    (scalarRow13146.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13146.table (sourceIndex j)).centre) /
      (scalarRow13146.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13146.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13146,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13146,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13146,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13146,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13146,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13146,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13146,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13146,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13146,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13146,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13146,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13146,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13146,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13146,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13146,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13146,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13146,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13146,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13146,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13146,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13146,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13146,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13146,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13146,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13146,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13146,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13146,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13146,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13146,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13146,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13146,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13146,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13146,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13146,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13146,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13146,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13146,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13146,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13146,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13146,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13146,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13146,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13146,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13146,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13146,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13146,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13146,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13146,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13146,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13146,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13146,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13146,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13146,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13146,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13146,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13146,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13146,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13146,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13146,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13146,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13146,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13146,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13146,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13146,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13146,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13146,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13146,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13146,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13146,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13146,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13146,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13146,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13146,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13146,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13146,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13146,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13146,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13146,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13146,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13146,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13146,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13146,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13146,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13146,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13146,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13146,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13146 : FrameRepair 13146 scalarRow13146 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13146Cells j).1 (repair13146Cells j).2.1
  endpoint_upper := fun j => ((repair13146Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13146Cells j).2.2

theorem repair13147Cells (j : Fin 43) :
    0 ≤ (scalarRow13147.table (sourceIndex j)).upper ∧
    (scalarRow13147.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13147.table (sourceIndex j)).centre) /
      (scalarRow13147.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13147.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13147,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13147,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13147,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13147,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13147,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13147,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13147,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13147,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13147,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13147,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13147,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13147,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13147,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13147,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13147,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13147,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13147,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13147,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13147,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13147,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13147,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13147,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13147,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13147,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13147,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13147,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13147,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13147,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13147,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13147,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13147,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13147,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13147,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13147,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13147,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13147,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13147,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13147,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13147,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13147,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13147,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13147,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13147,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13147,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13147,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13147,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13147,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13147,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13147,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13147,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13147,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13147,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13147,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13147,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13147,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13147,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13147,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13147,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13147,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13147,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13147,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13147,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13147,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13147,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13147,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13147,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13147,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13147,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13147,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13147,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13147,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13147,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13147,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13147,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13147,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13147,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13147,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13147,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13147,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13147,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13147,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13147,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13147,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13147,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13147,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13147,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13147 : FrameRepair 13147 scalarRow13147 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13147Cells j).1 (repair13147Cells j).2.1
  endpoint_upper := fun j => ((repair13147Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13147Cells j).2.2

theorem repair13148Cells (j : Fin 43) :
    0 ≤ (scalarRow13148.table (sourceIndex j)).upper ∧
    (scalarRow13148.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13148.table (sourceIndex j)).centre) /
      (scalarRow13148.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13148.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13148,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13148,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13148,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13148,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13148,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13148,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13148,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13148,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13148,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13148,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13148,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13148,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13148,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13148,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13148,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13148,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13148,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13148,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13148,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13148,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13148,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13148,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13148,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13148,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13148,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13148,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13148,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13148,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13148,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13148,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13148,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13148,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13148,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13148,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13148,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13148,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13148,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13148,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13148,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13148,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13148,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13148,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13148,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13148,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13148,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13148,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13148,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13148,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13148,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13148,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13148,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13148,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13148,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13148,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13148,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13148,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13148,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13148,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13148,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13148,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13148,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13148,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13148,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13148,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13148,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13148,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13148,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13148,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13148,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13148,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13148,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13148,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13148,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13148,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13148,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13148,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13148,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13148,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13148,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13148,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13148,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13148,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13148,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13148,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13148,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13148,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13148 : FrameRepair 13148 scalarRow13148 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13148Cells j).1 (repair13148Cells j).2.1
  endpoint_upper := fun j => ((repair13148Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13148Cells j).2.2

theorem repair13149Cells (j : Fin 43) :
    0 ≤ (scalarRow13149.table (sourceIndex j)).upper ∧
    (scalarRow13149.table (sourceIndex j)).upper ≤ (scalarRow12350.table (sourceIndex j)).upper ∧
    (cap12350 j + (scalarRow13149.table (sourceIndex j)).centre) /
      (scalarRow13149.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13149.targetFrame := by
  match j with
  | ⟨0,_⟩ => norm_num [scalarRow13149,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13149,BstLean.Part268.cell12350,cap12350]
  | ⟨1,_⟩ => norm_num [scalarRow13149,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13149,BstLean.Part268.cell12350,cap12350]
  | ⟨2,_⟩ => norm_num [scalarRow13149,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13149,BstLean.Part268.cell12350,cap12350]
  | ⟨3,_⟩ => norm_num [scalarRow13149,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13149,BstLean.Part268.cell12350,cap12350]
  | ⟨4,_⟩ => norm_num [scalarRow13149,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13149,BstLean.Part268.cell12350,cap12350]
  | ⟨5,_⟩ => norm_num [scalarRow13149,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13149,BstLean.Part268.cell12350,cap12350]
  | ⟨6,_⟩ => norm_num [scalarRow13149,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13149,BstLean.Part268.cell12350,cap12350]
  | ⟨7,_⟩ => norm_num [scalarRow13149,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13149,BstLean.Part268.cell12350,cap12350]
  | ⟨8,_⟩ => norm_num [scalarRow13149,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13149,BstLean.Part268.cell12350,cap12350]
  | ⟨9,_⟩ => norm_num [scalarRow13149,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13149,BstLean.Part268.cell12350,cap12350]
  | ⟨10,_⟩ => norm_num [scalarRow13149,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13149,BstLean.Part268.cell12350,cap12350]
  | ⟨11,_⟩ => norm_num [scalarRow13149,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13149,BstLean.Part268.cell12350,cap12350]
  | ⟨12,_⟩ => norm_num [scalarRow13149,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13149,BstLean.Part268.cell12350,cap12350]
  | ⟨13,_⟩ => norm_num [scalarRow13149,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13149,BstLean.Part268.cell12350,cap12350]
  | ⟨14,_⟩ => norm_num [scalarRow13149,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13149,BstLean.Part268.cell12350,cap12350]
  | ⟨15,_⟩ => norm_num [scalarRow13149,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13149,BstLean.Part268.cell12350,cap12350]
  | ⟨16,_⟩ => norm_num [scalarRow13149,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13149,BstLean.Part268.cell12350,cap12350]
  | ⟨17,_⟩ => norm_num [scalarRow13149,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13149,BstLean.Part268.cell12350,cap12350]
  | ⟨18,_⟩ => norm_num [scalarRow13149,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13149,BstLean.Part268.cell12350,cap12350]
  | ⟨19,_⟩ => norm_num [scalarRow13149,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13149,BstLean.Part268.cell12350,cap12350]
  | ⟨20,_⟩ => norm_num [scalarRow13149,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13149,BstLean.Part268.cell12350,cap12350]
  | ⟨21,_⟩ => norm_num [scalarRow13149,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13149,BstLean.Part268.cell12350,cap12350]
  | ⟨22,_⟩ => norm_num [scalarRow13149,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13149,BstLean.Part268.cell12350,cap12350]
  | ⟨23,_⟩ => norm_num [scalarRow13149,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13149,BstLean.Part268.cell12350,cap12350]
  | ⟨24,_⟩ => norm_num [scalarRow13149,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13149,BstLean.Part268.cell12350,cap12350]
  | ⟨25,_⟩ => norm_num [scalarRow13149,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13149,BstLean.Part268.cell12350,cap12350]
  | ⟨26,_⟩ => norm_num [scalarRow13149,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13149,BstLean.Part268.cell12350,cap12350]
  | ⟨27,_⟩ => norm_num [scalarRow13149,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13149,BstLean.Part268.cell12350,cap12350]
  | ⟨28,_⟩ => norm_num [scalarRow13149,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13149,BstLean.Part268.cell12350,cap12350]
  | ⟨29,_⟩ => norm_num [scalarRow13149,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13149,BstLean.Part268.cell12350,cap12350]
  | ⟨30,_⟩ => norm_num [scalarRow13149,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13149,BstLean.Part268.cell12350,cap12350]
  | ⟨31,_⟩ => norm_num [scalarRow13149,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13149,BstLean.Part268.cell12350,cap12350]
  | ⟨32,_⟩ => norm_num [scalarRow13149,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13149,BstLean.Part268.cell12350,cap12350]
  | ⟨33,_⟩ => norm_num [scalarRow13149,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13149,BstLean.Part268.cell12350,cap12350]
  | ⟨34,_⟩ => norm_num [scalarRow13149,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13149,BstLean.Part268.cell12350,cap12350]
  | ⟨35,_⟩ => norm_num [scalarRow13149,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13149,BstLean.Part268.cell12350,cap12350]
  | ⟨36,_⟩ => norm_num [scalarRow13149,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13149,BstLean.Part268.cell12350,cap12350]
  | ⟨37,_⟩ => norm_num [scalarRow13149,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13149,BstLean.Part268.cell12350,cap12350]
  | ⟨38,_⟩ => norm_num [scalarRow13149,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13149,BstLean.Part268.cell12350,cap12350]
  | ⟨39,_⟩ => norm_num [scalarRow13149,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13149,BstLean.Part268.cell12350,cap12350]
  | ⟨40,_⟩ => norm_num [scalarRow13149,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13149,BstLean.Part268.cell12350,cap12350]
  | ⟨41,_⟩ => norm_num [scalarRow13149,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13149,BstLean.Part268.cell12350,cap12350]
  | ⟨42,_⟩ => norm_num [scalarRow13149,scalarRow12350,sourceIndex,
      BstLean.Part268.cell13149,BstLean.Part268.cell12350,cap12350]
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13149 : FrameRepair 13149 scalarRow13149 where
  cap := cap12350
  cap_nonneg := repair12350.cap_nonneg
  cap_mono := repair12350.cap_mono
  endpoint := fun j => common_cap_bound (by norm_num) j
    (repair13149Cells j).1 (repair13149Cells j).2.1
  endpoint_upper := fun j => ((repair13149Cells j).2.1).trans (repair12350.endpoint_upper j)
  frame := fun j => (repair13149Cells j).2.2

end BstLean.Part269
